(ns klara.runtime.account
  "Accounts (design/10-accounting.md, spec/L3-effects.md#accounts): resource
  vectors, wallets and tokens.

  A resource vector is a map from keywords to exact non-negative amounts
  (L3.account.vector). The session and every job have a wallet
  (L3.account.wallet): an atom outside the job record, so nothing that
  resets a job (an abandoned host call) refunds what was spent, holding

    {:balance v :spent v :minted v :live {Token v} :settled bool}

  `:steps` is never in these vectors: a wallet's steps are its job's meter
  (a long-array ticked by the machine, L3.budget.steps), and the session has
  no meter, so its steps are unlimited and are not accounted.

  A token is a Token object (klara.runtime.value) naming the wallet it was
  taken in (L3.account.token); what it holds is the wallet's `:live` entry
  for it. An operation that consumes a token removes that entry, so a second
  use finds nothing (L3.affine.reuse), and using a token in another wallet
  is refused (L3.account.foreign). Every change is one swap! whose function
  validates first and throws, leaving the wallet unchanged."
  (:require [klara.lang.builtins :as b]
            [klara.runtime.machine :as m]
            [klara.runtime.value :as v])
  (:import [java.util UUID]
           [java.util.concurrent ThreadLocalRandom]
           [java.util.concurrent.atomic AtomicLong]
           [klara.runtime.value Token]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; ---------------------------------------------------------------------------
;; Resource vectors (L3.account.vector)

(defn- amount [k x]
  (let [a (cond (integer? x) x
                (ratio? x) x
                (decimal? x) (rationalize x)
                :else (fail :L3.account.vector
                            (str "the amount of " k " must be an exact number, not " (pr-str x))))]
    (when (neg? a) (fail :L3.account.vector (str "the amount of " k " is negative: " (pr-str x))))
    (when (and (= k :steps) (not (and (integer? a) (<= a Long/MAX_VALUE))))
      (fail :L3.account.vector (str ":steps must be a whole number of steps, not " (pr-str x))))
    a))

(defn vector!
  "Normalize and check a resource vector: exact amounts, decimals as ratios,
   zero entries dropped."
  [x]
  (when-not (map? x)
    (fail :L3.account.vector (str "a resource vector is a map from keywords to amounts, not " (pr-str x))))
  (reduce-kv (fn [acc k a]
               (when-not (keyword? k)
                 (fail :L3.account.vector (str "a resource is named by a keyword, not " (pr-str k))))
               (let [a (amount k a)] (if (zero? a) acc (assoc acc k a))))
             {} x))

(defn v+ [a b] (reduce-kv (fn [acc k x] (assoc acc k (+' (get acc k 0) x))) a b))

(defn v-
  "a − b, for b ≤ a."
  [a b]
  (reduce-kv (fn [acc k x]
               (let [r (-' (get acc k 0) x)] (if (zero? r) (dissoc acc k) (assoc acc k r))))
             a b))

(defn v<= [a b] (every? (fn [[k x]] (<= x (get b k 0))) a))

(defn scale [v n] (into {} (map (fn [[k x]] [k (*' x n)])) v))

(defn- steps-of ^long [v] (long (get v :steps 0)))

;; ---------------------------------------------------------------------------
;; Wallets (L3.account.wallet)

(deftype Wallet [^long id parent state meter])

(defonce ^:private ids (AtomicLong.))

(def ^:private empty-state {:balance {} :spent {} :minted {} :live {} :settled false})

(defn root-wallet [] (Wallet. (.incrementAndGet ^AtomicLong ids) nil (atom empty-state) nil))

(defn child-wallet
  "A job's wallet holding `balance` (without :steps); its steps are `meter`."
  [parent meter balance]
  (Wallet. (.incrementAndGet ^AtomicLong ids) parent (atom (assoc empty-state :balance balance)) meter))

(defn state [^Wallet w] @(.-state w))

(defn- current ^Wallet [st]
  (or (get-in st [:dyn :wallet]) (fail :L3.account.wallet "there is no wallet in this context")))

(defn- meter-steps ^long [^Wallet w] (if-let [^longs m (.-meter w)] (max 0 (aget m 0)) Long/MAX_VALUE))

(defn- check-steps! [^Wallet w ^long n]
  (when (and (.-meter w) (> n (meter-steps w)))
    (fail :L3.account.insufficient (str "the budget has " (meter-steps w) " steps left, not " n))))

(defn- withdraw-steps! [^Wallet w ^long n]
  (when-let [^longs m (.-meter w)] (aset m 0 (- (aget m 0) n))))

(defn- deposit-steps! [^Wallet w ^long n]
  (when-let [^longs m (.-meter w)] (aset m 0 (+ (max 0 (aget m 0)) n))))

(defn- insufficient [what has wants]
  (fail :L3.account.insufficient (str what " holds " (pr-str has) ", not " (pr-str wants))
        :holds has :wants wants))

(defn withdraw!
  "Take `v` (without :steps) out of the wallet's balance."
  [^Wallet w v]
  (swap! (.-state w) (fn [s]
                       (when-not (v<= v (:balance s)) (insufficient "the wallet" (:balance s) v))
                       (update s :balance v- v))))

(defn- spend-steps-and [^Wallet w v f]
  (let [n (steps-of v)]
    (check-steps! w n)
    (let [r (swap! (.-state w) f)]
      (withdraw-steps! w n)
      r)))

;; ---------------------------------------------------------------------------
;; Tokens (L3.account.token)

(defn token? [x] (instance? Token x))

(defn- token! [^Wallet w] (Token. (.-id w)))

(defn- held
  "What token `t` holds in wallet state `s`, checking foreign before reuse."
  [^Wallet w s t]
  (when-not (instance? Token t)
    (fail :L3.account.token (str "not an account token: " (pr-str t))))
  (when-not (= (.-owner ^Token t) (.-id w))
    (fail :L3.account.foreign "this token belongs to another job's wallet"))
  (or (get (:live s) t)
      (fail :L3.affine.reuse "this token was already used: an operation consumed it"
            :hint (str "a second alias, collection or closure, or a continuation resumed twice "
                       "(L3.cont.context): pass each resumption its own token, or run each "
                       "branch as a job with its own budget"))))

(defn- swap-held!
  "Swap the wallet with (f s held-vector); returns f's second value."
  [^Wallet w t f]
  (let [out (volatile! nil)]
    (swap! (.-state w) (fn [s] (let [[s' r] (f s (held w s t))] (vreset! out r) s')))
    @out))

(defn consume!
  "Consume token `t` of wallet `w`, returning what it held."
  [^Wallet w t]
  (swap-held! w t (fn [s held] [(update s :live dissoc t) held])))

(defn take!
  [^Wallet w v]
  (let [t (token! w) rest (dissoc v :steps)]
    (spend-steps-and w v (fn [s]
                           (when-not (v<= rest (:balance s)) (insufficient "the wallet" (:balance s) rest))
                           (-> s (update :balance v- rest) (assoc-in [:live t] v))))
    t))

(defn spend [^Wallet w t v]
  (let [t2 (token! w)]
    (swap-held! w t (fn [s held]
                      (when-not (v<= v held) (insufficient "the token" held v))
                      [(-> s (update :live dissoc t) (assoc-in [:live t2] (v- held v))
                           (update :spent v+ (dissoc v :steps)))
                       t2]))))

(defn split [^Wallet w t v]
  (let [t1 (token! w) t2 (token! w)]
    (swap-held! w t (fn [s held]
                      (when-not (v<= v held) (insufficient "the token" held v))
                      [(-> s (update :live dissoc t) (assoc-in [:live t1] v) (assoc-in [:live t2] (v- held v)))
                       [t1 t2]]))))

(defn join [^Wallet w t1 t2]
  (when (identical? t1 t2)
    (fail :L3.affine.reuse "join was given the same token twice"))
  (let [t (token! w)]
    (swap-held! w t1 (fn [s h1]
                       (let [h2 (held w s t2)]
                         [(-> s (update :live dissoc t1 t2) (assoc-in [:live t] (v+ h1 h2))) t])))))

(defn put! [^Wallet w t]
  (let [v (swap-held! w t (fn [s held]
                            [(-> s (update :live dissoc t) (update :balance v+ (dissoc held :steps))) held]))]
    (deposit-steps! w (steps-of v))
    nil))

(defn holds? [^Wallet w t v] (v<= v (held w (state w) t)))

(defn balance [^Wallet w t] (held w (state w) t))

;; ---------------------------------------------------------------------------
;; Budgets and settlement (L3.account.wallet, L3.account.settle)

(defn- reserve-steps
  "Reserve up to n steps from `meter` (L3.budget.nesting); nil is unlimited."
  ^long [meter ^long n]
  (if-let [^longs pm meter]
    (let [r (min n (max 0 (aget pm 0)))] (aset pm 0 (- (aget pm 0) r)) r)
    n))

(defn grant!
  "Reserve a job's budget in context `dyn`: a vector, a token (consumed:
   the only way a token crosses a job boundary), or nil. Steps missing from
   the budget are `default-steps`; they are reserved up to what the meter
   has, as before. `withdrawn` is a non-step part already taken (run-all).
   Returns the grant, a vector with :steps."
  [dyn budget ^long default-steps withdrawn]
  (let [^Wallet w (:wallet dyn)
        meter (:meter dyn)]
    (cond
      withdrawn
      (assoc withdrawn :steps (reserve-steps meter (long (get (vector! (or budget {})) :steps default-steps))))

      (instance? Token budget)
      (let [held (consume! (or w (fail :L3.account.wallet "there is no wallet in this context")) budget)]
        (assoc held :steps (if (contains? held :steps) (steps-of held) (reserve-steps meter default-steps))))

      :else
      (let [v (vector! (or budget {}))
            rest (dissoc v :steps)]
        (when (seq rest)
          (withdraw! (or w (insufficient "the context" {} rest)) rest))
        (assoc rest :steps (reserve-steps meter (long (get v :steps default-steps))))))))

(defn- receipt-id []
  (let [r (ThreadLocalRandom/current)] (UUID. (.nextLong r) (.nextLong r))))

(defn- posting [kind src dst v]
  (let [v (into {} (remove (comp zero? val)) v)]
    (when (seq v) {:kind kind :source src :destination dst :resources v})))

(defn settle!
  "End job wallet `w` (L3.account.settle): live tokens return to it, what it
   spent is charged to its parent and the rest returns to the parent's
   wallet and to `parent-meter`. Returns the receipt (L3.account.receipt)."
  [^Wallet w parent-meter granted]
  (let [^longs m (.-meter w)
        _ (aset m 0 (max 0 (aget m 0)))
        [old _] (swap-vals! (.-state w) (fn [s] (assoc s :live {} :settled true)))
        lives (vals (:live old))
        rest (reduce (fn [acc h] (v+ acc (dissoc h :steps))) (:balance old) lives)
        steps-left (long (+ (aget m 0) (long (reduce + 0 (map steps-of lives)))))
        spent (:spent old)]
    (aset m 0 steps-left)
    (when-let [^Wallet p (.-parent w)]
      (swap! (.-state p) (fn [s] (-> s (update :balance v+ rest) (update :spent v+ spent)))))
    (when-let [^longs pm parent-meter] (aset pm 0 (long (+ (aget pm 0) steps-left))))
    (let [granted granted
          spent (assoc spent :steps (- (steps-of granted) steps-left))
          returned (assoc rest :steps steps-left)]
      {:id (receipt-id) :granted granted :spent spent :returned returned
       :postings (filterv some? [(posting :grant :parent :job granted)
                                 (posting :consume :job :sink spent)
                                 (posting :return :job :parent returned)])})))

;; ---------------------------------------------------------------------------
;; The program-facing operations (klara.account)

(defn- ret [st x] (assoc st :mode :ret :ctl x :env nil))

(defmacro ^:private defop [q args & body]
  `(b/register! '~q {:kind :intrinsic :fn (fn [~'st ~args] (ret ~'st (do ~@body)))}))

(defop klara.account/mint! [v]                                         ; L3.account.mint
  (when (get-in st [:dyn :job]) (fail :L3.account.mint "only the session mints; a job cannot create resources"))
  (let [v (vector! v) ^Wallet w (current st)]
    (when (contains? v :steps) (fail :L3.account.mint "steps are not minted: a job's steps are its budget"))
    (swap! (.-state w) (fn [s] (-> s (update :balance v+ v) (update :minted v+ v))))
    nil))

(defop klara.account/spend! [v]                                        ; L3.account.wallet
  (let [v (vector! v) ^Wallet w (current st) rest (dissoc v :steps)]
    (spend-steps-and w v (fn [s]
                           (when-not (v<= rest (:balance s)) (insufficient "the wallet" (:balance s) rest))
                           (-> s (update :balance v- rest) (update :spent v+ rest))))
    nil))

(defop klara.account/wallet []
  (let [^Wallet w (current st) b (:balance (state w))]
    (if (.-meter w) (assoc b :steps (meter-steps w)) b)))

(defop klara.account/take [v] (take! (current st) (vector! v)))      ; L3.account.token
(defop klara.account/spend [t v] (spend (current st) t (vector! v)))
(defop klara.account/split [t v] (split (current st) t (vector! v))) ; L3.account.split
(defop klara.account/join [t1 t2] (join (current st) t1 t2))
(defop klara.account/put [t] (put! (current st) t))
(defop klara.account/holds? [t v] (holds? (current st) t (vector! v))) ; L3.account.holds
(defop klara.account/balance [t] (balance (current st) t))
(defop klara.account/token? [x] (token? x))

;; ---------------------------------------------------------------------------
;; The token operations for compiled code (L4.check.affine-erase): the same
;; operations on the wallet of the running machine's context, which the
;; machine sets before it enters compiled code. Each keeps its checks: in
;; this representation the lookup that finds a token's amount is the reuse
;; check, so there is nothing to erase until tokens are unboxed.

(defn- context-wallet ^Wallet []
  (let [^objects c (m/current-context)]
    (or (and c (:wallet (aget c 2))) (fail :L3.account.wallet "there is no wallet in this context"))))

(defn take-c [v] (take! (context-wallet) (vector! v)))
(defn spend-c [t v] (spend (context-wallet) t (vector! v)))
(defn split-c [t v] (split (context-wallet) t (vector! v)))
(defn join-c [t1 t2] (join (context-wallet) t1 t2))
(defn put-c [t] (put! (context-wallet) t))
(defn holds-c? [t v] (holds? (context-wallet) t (vector! v)))
(defn balance-c [t] (balance (context-wallet) t))

(def compiled
  "Account operations compiled code calls directly (klara.compile.lower)."
  '{klara.account/take klara.runtime.account/take-c
    klara.account/spend klara.runtime.account/spend-c
    klara.account/split klara.runtime.account/split-c
    klara.account/join klara.runtime.account/join-c
    klara.account/put klara.runtime.account/put-c
    klara.account/holds? klara.runtime.account/holds-c?
    klara.account/balance klara.runtime.account/balance-c
    klara.account/token? klara.runtime.account/token?})
