(ns klara.authority
  "Authorities (RFC 0001, doc/background/01-core-v2.md §2): the store,
  the split rules of fork and fork-resume, and settlement.

  DATA IS ALIASABLE; AUTHORITY IS NOT. An authority value (an Auth) is
  plain data: an id and a kind. It may be referenced any number of times,
  put in collections or metadata, captured by closures, defined in the
  world. What cannot be duplicated is its USE: every use goes through the
  STORE, which holds the one state of each authority,

    {:id n :kind k :status s :operation op :scope ctx-id :owner label
     :gen g :payload {..}}

  and serializes its transitions (generation g counts them). Kinds:
    :resource    a host object; consume, use; never split (transfer only)
    :evidence    likelihood mass {:mass :spent :moved}; spend, split, join
    :budget      components {:mass {c n} :spent {c n} :moved {c n} :hard #{c}}
    :randomness  a splittable key {:key k}; draw
    :branchable  settlement authority over branches of systems (worlds)
                 {:systems {sid {:parent World :child World :base root}}};
                 merge, discard, transfer, partition, advance (spindel's
                 ForkHandle)
  Lifecycle: :open -> :advancing (leased: an operation in flight, or the
  authority is lent to a running fork) -> :settled (with the :operation
  that settled it) | :incomplete (failure after a durable mutation began).

  BRANCH CONTEXTS. Code runs under a chain of contexts, read from the
  machine's continuation: every {:tag :branch :ctx c} frame, innermost
  first. A fork creates one context per branch; resuming a continuation
  a second time (fork-resume) runs it under a fresh :shot context. A token
  belongs to the context it was minted in (:scope). Using a token from
  inside a context that does not own it RESOLVES it: the context derives
  its own child token from the parent's, once, by the split rule of the
  kind, and keeps using the child (subst). So an alias reached by any
  route - a local, a collection, metadata, a closure, a world lookup
  after capture - is checked when it is used, not when it is copied.

  Split rules (fork of n branches | fork-resume shot):
    resource    child only in the branch it was transferred to | rejected
    evidence    mass split by :shares (equal by default) | rejected: the
                number of shots is unknown, split explicitly (join-then-split)
    budget      every component split by :shares; hard components cannot
                be overspent | the shot borrows the remaining budget
    randomness  key split per branch, the same key under :coupled | split
    branchable  branch! per branch; adopting one merges it, the others are
                discarded (settlement is partitioned) | branch!, discarded
  While children exist the parent is leased (:advancing). When the fork
  scope exits, children are settled and the parent reopens: evidence spent
  in the adopted branch is committed, evidence spent in discarded branches
  is refunded (mass is conserved, AU6); budget spent in any branch is
  charged (it cannot be undone); an unconsumed resource returns.

  IRREVERSIBLE EFFECTS. A host call classified irreversible (println,
  spit, swap!, ..) inside a fork branch is deferred as an Intent, run when
  the branch is adopted and dropped when it is discarded (AU5). Running
  one directly needs a capability (a resource authority, so only the one
  branch it is transferred to can use it) and leaves a receipt.

  The machine glue (frames, fork-resume detection) is in klara.eval."
  (:require [clojure.string :as str]
            [klara.world :as w]))

;; ---------------------------------------------------------------------------
;; values
;; ---------------------------------------------------------------------------

(deftype Auth [id kind]
  Object
  (equals [_ o] (and (instance? Auth o) (= id (.-id ^Auth o))))
  (hashCode [_] (hash [::auth id])))

(defn auth? [x] (instance? Auth x))
(defn auth-id [^Auth t] (.-id t))

;; A deferred irreversible effect.
(deftype Intent [op args])

;; The result of one fork branch: (:value b), (:index b).
(deftype Branch [ctx index value]
  clojure.lang.ILookup
  (valAt [this k] (.valAt this k nil))
  (valAt [_ k nf] (case k :value value :index index nf)))

(defn branch? [x] (instance? Branch x))

(defmethod print-method Auth [^Auth t ^java.io.Writer wr]
  (.write wr (str "#<" (name (.-kind t)) ">")))
(defmethod print-method Intent [^Intent i ^java.io.Writer wr]
  (.write wr (str "#<intent " (first (.-args i)) ">")))
(defmethod print-method Branch [^Branch b ^java.io.Writer wr]
  (.write wr (str "#<branch " (.-index b) ">")))

;; ---------------------------------------------------------------------------
;; the store
;; ---------------------------------------------------------------------------

(defn new-store
  "A fresh authority store. :minted totals the evidence mass minted and
  not discarded (the AU6 audit compares it with the mass tokens hold)."
  []
  (atom {:next 0 :tokens {} :receipts [] :minted {:evidence 0}}))

(defonce global-store (new-store))

(def ^:dynamic *store*
  "The store authority operations act on. A REPL session binds its own."
  global-store)

(def ^:dynamic *mutation-hook*
  "nil, or (fn [operation system-id]) called before each durable mutation
  of a settlement or advance (tests inject failures and races here)."
  nil)

(defn- fail [msg & [data]]
  (throw (ex-info (str "klara: " msg) (merge {:klara/error :authority} data))))

(defn state
  "The store state of a token (an Auth or an id)."
  [t]
  (let [id (if (auth? t) (auth-id t) t)]
    (or (get-in @*store* [:tokens id])
        (fail "unknown authority (minted in another store?)" {:id id}))))

(defn- put! [id f]
  (swap! *store* update-in [:tokens id] (fn [s] (update (f s) :gen inc))))

(defn receipt! [r] (swap! *store* update :receipts conj r) nil)

(defn receipts [] (:receipts @*store*))

;; ---------------------------------------------------------------------------
;; contexts
;; ---------------------------------------------------------------------------

(defonce ^:private ctx-counter (atom 0))

(defn- new-ctx [mode group index]
  {:id [:ctx (swap! ctx-counter inc)] :mode mode :group group :index index
   :subst (atom {}) :owned (atom []) :intents (atom []) :closed (atom false)})

(defn ctx-chain
  "Branch contexts of a sequence of frames, innermost first."
  [frames]
  (keep #(when (= :branch (:tag %)) (:ctx %)) frames))

(defn ctx-open? [ctx] (not @(:closed ctx)))
(defn group-open? [g] (not (:closed @g)))

(defn shot-frame
  "The frame under which a continuation resumed a second time runs."
  []
  (let [g (atom {:n 1 :mode :shot :leases {} :closed false})
        c (new-ctx :shot g 0)]
    (swap! g assoc :ctxs [c])
    {:tag :branch :ctx c}))

(defn- mint! [kind payload chain & [extra]]
  (let [ctx (first chain)
        st (swap! *store*
                  (fn [s]
                    (let [id (inc (:next s))]
                      (-> s
                          (assoc :next id)
                          (assoc-in [:tokens id]
                                    (merge {:id id :kind kind :status :open :scope (:id ctx)
                                            :gen 0 :payload payload :origin :mint}
                                           extra))))))
        id (:next st)]
    (when ctx (swap! (:owned ctx) conj id))
    (Auth. id kind)))

;; ---------------------------------------------------------------------------
;; keys (MINSTD, as in examples/klara)
;; ---------------------------------------------------------------------------

(def ^:private M 2147483647)
(defn- next-key [k] (mod (* 48271 k) M))
(defn- split-key [k i] (next-key (mod (+ (* 1000003 k) i 1) M)))

;; ---------------------------------------------------------------------------
;; component arithmetic (budgets)
;; ---------------------------------------------------------------------------

(defn- n*
  "Exact product; integral results as longs (shares print as 5, not 5N)."
  [a b]
  (let [x (* a b)]
    (if (and (instance? clojure.lang.BigInt x) (< (abs (double x)) 9.0E18)) (long x) x)))

(defn- c+ [a b] (merge-with + a b))
(defn- c- [a b] (merge-with + a (update-vals b -)))
(defn- c* [a x] (update-vals a #(n* % x)))
(defn- czero [a] (update-vals a (constantly 0)))

(defn- remaining* [{:keys [kind payload]}]
  (case kind
    :evidence (- (:mass payload) (:spent payload) (:moved payload))
    :budget (c- (c- (:mass payload) (:spent payload)) (:moved payload))
    nil))

;; ---------------------------------------------------------------------------
;; lazy derivation: the split rules
;; ---------------------------------------------------------------------------

(defn- weights [g pid]
  (let [n (:n @g)
        ws (get (:shares @g) pid)]
    (if ws
      (let [s (reduce + ws)] (mapv #(/ % s) ws))
      (vec (repeat n (/ 1 n))))))

(defn- children-for
  "Mint the n children of parent state st for group g. Returns
  [child-ids-or-nil lease-extra parent-update-fn]."
  [g st]
  (let [{:keys [n mode ctxs coupled transfer]} @g
        shot? (= :shot mode)
        pid (:id st)
        kmint (fn [i payload]
                (let [ctx (nth ctxs i)
                      t (mint! (:kind st) payload nil {:scope (:id ctx) :origin :derived
                                                       :derived-from pid})]
                  (auth-id t)))]
    (case (:kind st)
      :resource
      (if shot?
        (fail "fork-resume: a resumed continuation uses a resource authority; it can be resumed only once")
        (if-let [i (get transfer pid)]
          [(assoc (vec (repeat n nil)) i (kmint i (:payload st))) {} identity]
          (fail "resource authority was not transferred to this branch (a fork must transfer it to exactly one branch)")))

      :evidence
      (if shot?
        (fail "fork-resume: a resumed continuation uses an evidence authority; the number of shots is unknown, so split it explicitly before resuming (join-then-split)")
        (let [r (remaining* st)
              ws (weights g pid)]
          [(vec (map-indexed (fn [i wt] (kmint i {:mass (n* r wt) :spent 0 :moved 0})) ws))
           {:lent r}
           #(update-in % [:payload :moved] + r)]))

      :budget
      (let [r (remaining* st)
            ws (if shot? [1] (weights g pid))
            hard (get-in st [:payload :hard])]
        [(vec (map-indexed (fn [i wt] (kmint i {:mass (c* r wt) :spent (czero r) :moved (czero r)
                                                 :hard hard}))
                           ws))
         {:lent r}
         #(update-in % [:payload :moved] c+ r)])

      :randomness
      (let [k (get-in st [:payload :key])
            coupled? (or (true? coupled) (contains? coupled pid))]
        [(vec (for [i (range n)] (kmint i {:key (if (and coupled? (not shot?)) k (split-key k i))})))
         {}
         #(assoc-in % [:payload :key] (split-key k n))])

      :branchable
      [(vec (for [i (range n)]
              (kmint i {:systems (into {} (for [[sid {:keys [child]}] (get-in st [:payload :systems])
                                                :let [c (w/fork child)]]
                                            [sid {:parent child :child c :base (w/snapshot c)}]))})))
       {}
       identity])))

(defn- derive! [ctx pid]
  (let [g (:group ctx)
        i (:index ctx)]
    (when-not (ctx-open? ctx)
      (fail "this branch has closed; its authorities are settled"))
    (if-let [l (get-in @g [:leases pid])]
      (or (nth (:children l) i)
          (fail "resource authority was not transferred to this branch (a fork must transfer it to exactly one branch)"))
      (let [st (state pid)]
        (when (and (= :shot (:mode @g)) (#{:resource :evidence} (:kind st)))
          (children-for g st))          ; refuses with the fork-resume reason
        (when-not (= :open (:status st))
          (fail (str "authority is " (name (:status st))
                     (when-let [op (:operation st)] (str " (" (name op) ")")))
                {:status (:status st)}))
        (let [[children extra upd] (children-for g st)]
          (put! pid #(-> (upd %) (assoc :status :advancing
                                        :operation (if (= :shot (:mode @g)) :fork-resume :fork))))
          (swap! g assoc-in [:leases pid] (merge {:kind (:kind st) :children children} extra))
          (or (nth children i)
              (fail "resource authority was not transferred to this branch")))))))

(defn- resolve-id
  "The id of the token through which code under chain uses token id."
  [id chain]
  (let [{:keys [scope status]} (state id)]
    (cond
      (= scope (:id (first chain))) id
      (not (#{:open :advancing} status)) id     ; settled: the use reports how
      (empty? chain)
      (fail "authority belongs to a branch that is not running here (escaped from a fork, or a sibling branch)")
      :else
      (let [c (first chain)]
        (or (get @(:subst c) id)
            (let [pid (resolve-id id (rest chain))
                  cid (derive! c pid)]
              (swap! (:subst c) assoc id cid pid cid)
              cid))))))

(defn- peek-id
  "Like resolve-id but never derives (for status)."
  [id chain]
  (or (some #(get @(:subst %) id) chain) id))

(defn- token-id [t what]
  (if (auth? t) (auth-id t) (fail (str what " expects an authority, got " (pr-str t)))))

(defn- usable
  "Resolve t under chain; the state, which must be open and of a kind in kinds."
  [t chain kinds what]
  (let [id (resolve-id (token-id t what) chain)
        st (state id)]
    (when-not (contains? kinds (:kind st))
      (fail (str what " needs a " (str/join " or " (map name kinds))
                 " authority, got " (name (:kind st)))))
    (when-not (= :open (:status st))
      (fail (str what ": authority is " (name (:status st))
                 (when-let [op (:operation st)] (str " (" (name op) ")")))
            {:status (:status st) :operation (:operation st)}))
    st))

;; ---------------------------------------------------------------------------
;; settlement (spindel's ForkHandle protocol, S8-S10)
;; ---------------------------------------------------------------------------

(defn- claim!
  "open -> advancing (preflight). Repeating a completed merge or discard
  returns its result; anything else on a non-open authority fails."
  [id op]
  (let [st (state id)]
    (cond
      (= :open (:status st))
      (do (put! id #(-> % (assoc :status :advancing :operation op :phase :preflight)
                        (dissoc :last-error)))
          {:execute? true})

      (and (= :settled (:status st)) (= op (:operation st)) (#{:merge :discard} op))
      {:execute? false :result (:result st)}

      :else
      (fail (str (name op) "!: authority is " (name (:status st))
                 (when-let [o (:operation st)] (str " (" (name o) ")")))
            {:status (:status st) :operation (:operation st)}))))

(defn- fail-op! [id e]
  (put! id (fn [s]
             (if (= :preflight (:phase s))
               (-> s (assoc :status :open :last-error (ex-message e))
                   (dissoc :operation :phase) (update :attempts (fnil inc 0)))
               (-> s (assoc :status :incomplete :last-error (ex-message e))
                   (update :attempts (fnil inc 0)))))))

(defn- run-op!
  "Claim id for op, run preflight (read-only; failure reopens), then
  mutate (failure leaves :incomplete). finish maps the state on success."
  [id op preflight mutate finish]
  (let [{:keys [execute? result]} (claim! id op)]
    (if-not execute?
      result
      (let [plan (try (preflight) (catch Throwable e (fail-op! id e) (throw e)))
            _ (put! id #(assoc % :phase :mutating))
            res (try (mutate plan) (catch Throwable e (fail-op! id e) (throw e)))]
        (put! id #(-> (finish %) (dissoc :phase)))
        res))))

(defn- settled [op res] #(assoc % :status :settled :operation op :result res))

;; three-way merge of world roots -----------------------------------------------

(defn merge-roots
  "Apply the definitions ours changed since base onto theirs. A symbol
  changed differently on both sides is a conflict: {::conflict sym}."
  [base theirs ours]
  (if (identical? theirs base)
    ours
    (reduce (fn [r [sym e]]
              (let [b (w/entry* base sym)
                    t (w/entry* theirs sym)]
                (cond
                  (identical? e b) r
                  (identical? t e) r
                  (identical? t b) (w/put-entry r sym e)
                  :else (reduced {::conflict sym}))))
            theirs (sort-by key (:defs ours)))))

(defn- conflict! [sid r]
  (when-let [s (::conflict r)]
    (fail (str "conflict: " s " changed in the branch and in the parent of system " sid)
          {:conflict s :system sid})))

(defn- merge-handle! [id]
  (let [systems (get-in (state id) [:payload :systems])]
    (run-op! id :merge
             (fn []
               (into (sorted-map)
                     (for [[sid {:keys [parent child base]}] systems
                           :let [cur (w/snapshot parent)
                                 r (merge-roots base cur (w/snapshot child))]]
                       (do (conflict! sid r) [sid [cur r]]))))
             (fn [plan]
               (doseq [[sid [cur r]] plan]
                 (when *mutation-hook* (*mutation-hook* :merge sid))
                 (when-not (compare-and-set! (:root (get-in systems [sid :parent])) cur r)
                   (fail (str "the parent of system " sid " changed during the merge"))))
               {:merged (vec (keys plan))})
             #(assoc % :status :settled :operation :merge :result {:merged (vec (sort (keys systems)))}))))

(defn- discard-handle! [id]
  (let [systems (get-in (state id) [:payload :systems])
        res {:discarded (vec (sort (keys systems)))}]
    (run-op! id :discard (constantly nil) (constantly res) (settled :discard res))))

;; ---------------------------------------------------------------------------
;; fork groups
;; ---------------------------------------------------------------------------

(defn group-ctx [g i] (nth (:ctxs @g) i))

(defn open-fork!
  "A group of n branch contexts for a fork under chain. opts: :coupled
  (true, or a collection of randomness authorities), :transfer {resource
  branch-index}, :shares {evidence-or-budget [weight ..]}."
  [opts n frames]
  (let [chain (ctx-chain frames)
        opts (or opts {})
        _ (when-not (map? opts) (fail "fork options must be a map"))
        res (fn [t what] (resolve-id (token-id t what) chain))
        transfer (into {} (for [[t i] (:transfer opts)]
                            (let [id (res t "fork :transfer")]
                              (when-not (and (int? i) (< -1 i n))
                                (fail "a resource is transferred to exactly one branch: give one branch index"))
                              (when-not (= :resource (:kind (state id)))
                                (fail "only resource authorities are transferred; other kinds are split"))
                              [id i])))
        shares (into {} (for [[t ws] (:shares opts)]
                          (do (when-not (and (sequential? ws) (= n (count ws))
                                             (every? #(and (number? %) (not (neg? %))) ws)
                                             (pos? (reduce + ws)))
                                (fail "fork :shares gives one nonnegative weight per branch"))
                              [(res t "fork :shares") (vec ws)])))
        coupled (let [c (:coupled opts)]
                  (cond (true? c) true
                        (or (nil? c) (false? c)) #{}
                        :else (into #{} (map #(res % "fork :coupled")) c)))
        g (atom {:n n :mode :fork :transfer transfer :shares shares :coupled coupled
                 :leases {} :adopted nil :closed false})]
    (swap! g assoc :ctxs (mapv #(new-ctx :fork g %) (range n)))
    ;; a transfer is an explicit move: the parent is leased at once
    (doseq [[id i] transfer]
      (let [c (group-ctx g i)]
        (swap! (:subst c) assoc id (derive! c id))))
    g))


(defn branches [g vals]
  (vec (map-indexed (fn [i v] (Branch. (group-ctx g i) i v)) vals)))

(defn adopt!
  "Mark branch b for adoption when its fork scope exits; returns its value."
  [b]
  (when-not (branch? b) (fail (str "adopt! expects a branch, got " (pr-str b))))
  (let [^Branch b b
        g (:group (.-ctx b))
        i (.-index b)]
    (when-not (group-open? g) (fail "adopt!: the fork that made this branch has closed"))
    (when-let [a (:adopted @g)]
      (when-not (= a i) (fail "adopt!: only one branch of a fork can be adopted")))
    (swap! g assoc :adopted i)
    (.-value b)))

(defn effect-mode
  "How an irreversible host effect runs under frames: [:direct cap-id],
  [:defer ctx] inside a fork branch, or nil (directly; no fork)."
  [frames]
  (some (fn [f]
          (case (:tag f)
            :direct [:direct (:cap-id f)]
            :branch (when (= :fork (:mode (:ctx f))) [:defer (:ctx f)])
            nil))
        frames))

(def ^:private irreversible-fns
  (atom '#{clojure.core/println clojure.core/print clojure.core/prn clojure.core/pr
           clojure.core/printf clojure.core/newline clojure.core/flush clojure.core/spit
           clojure.core/reset! clojure.core/swap! clojure.core/reset-vals!
           clojure.core/swap-vals! clojure.core/vreset! clojure.core/deliver
           clojure.core/send clojure.core/send-off}))

(defn classify-irreversible!
  "Classify host function sym as irreversible (deferred inside forks)."
  [sym]
  (swap! irreversible-fns conj sym)
  sym)

(defn irreversible? [sym]
  (and (symbol? sym)
       (or (contains? @irreversible-fns sym)
           (boolean (some-> (resolve sym) meta :klara/irreversible)))))

(defn defer!
  "Queue host call args ([sym & args]) as an intent of ctx."
  [ctx op args]
  (let [i (Intent. op (vec args))]
    (swap! (:intents ctx) conj i)
    i))

(defn- run-intents!
  "Run intents in order at an adoption with no enclosing fork."
  [intents branch]
  (let [n (count intents)]
    (doseq [[j ^Intent i] (map-indexed vector intents)
            :let [[sym & args] (.-args i)]]
      (try (apply @(requiring-resolve sym) args)
           (receipt! {:kind :intent :op sym :args (vec args) :branch branch})
           (catch Throwable e
             (receipt! {:kind :intent :op sym :args (vec args) :branch branch :status :failed})
             (fail (str "adoption incomplete: intent " (inc j) " of " n " (" sym ") failed: "
                        (ex-message e))
                   {:klara/error :incomplete}))))))

(defn- settle-child! [id]
  (put! id (fn [s]
             (cond-> (if (#{:open :advancing} (:status s))
                       (assoc s :status :settled :operation :fork-exit)
                       s)
               (= :evidence (:kind s)) (assoc-in [:payload :moved] (get-in s [:payload :mass]))))))

(defn- discard-owned! [id]
  (let [s (state id)]
    (when (and (= :evidence (:kind s)) (= :mint (:origin s)))
      (swap! *store* update-in [:minted :evidence] - (get-in s [:payload :mass])))
    (put! id (fn [s]
               (cond-> (if (#{:open :advancing} (:status s))
                         (assoc s :status :settled :operation :discard)
                         s)
                 (= :evidence (:kind s)) (assoc-in [:payload :moved] (get-in s [:payload :mass])))))))

(defn- rescope! [id chain]
  (let [p (first chain)]
    (put! id #(assoc % :scope (:id p)))
    (when p (swap! (:owned p) conj id))))

(defn close-group!
  "Settle group g at its scope exit under frames (the continuation below
  the scope). how: :exit (adopt the adopted branch, discard the others)
  or :abort (discard all: an exception left the fork). A shot adopts its
  one context except for branchable children, which it discards."
  [g frames how]
  (when (group-open? g)
    (swap! g assoc :closed true)
    (let [{:keys [mode ctxs leases]} @g
          chain (ctx-chain frames)
          shot? (= :shot mode)
          adopted (cond shot? 0 (= :abort how) nil :else (:adopted @g))
          errors (atom [])]
      (doseq [ctx ctxs] (reset! (:closed ctx) true))
      (doseq [[pid {:keys [kind children lent]}] leases]
        (let [ch (mapv #(some-> % state) children)
              a (when adopted (nth ch adopted))
              reopen #(-> % (assoc :status :open) (dissoc :operation))]
          (case kind
            :evidence
            (put! pid #(-> %
                           (update-in [:payload :moved] - lent)
                           (update-in [:payload :moved] + (or (get-in a [:payload :moved]) 0))
                           (update-in [:payload :spent] + (or (get-in a [:payload :spent]) 0))
                           reopen))
            :budget
            (let [spent (reduce c+ (czero lent) (keep #(get-in % [:payload :spent]) ch))]
              (put! pid #(-> %
                             (update-in [:payload :moved] c- lent)
                             (update-in [:payload :spent] c+ spent)
                             reopen)))
            :randomness (put! pid reopen)
            :resource
            (let [c (first (remove nil? ch))]
              (if (and c (= :settled (:status c)) (= :consume (:operation c)))
                (put! pid #(assoc % :status :settled :operation :consume))
                (put! pid reopen)))
            :branchable
            (do (doseq [[j cid] (map-indexed vector children)
                        :when cid
                        :let [st (state cid)]
                        :when (= :open (:status st))]
                  (if (and (= j adopted) (not shot?))
                    (try (merge-handle! cid)
                         (catch clojure.lang.ExceptionInfo e
                           (swap! errors conj e)
                           (when (= :open (:status (state cid))) (discard-handle! cid))))
                    (discard-handle! cid)))
                (put! pid reopen)))
          (doseq [c children :when c] (settle-child! c))))
      (doseq [[j ctx] (map-indexed vector ctxs)
              id @(:owned ctx)]
        (if (= j adopted) (rescope! id chain) (discard-owned! id)))
      (when (and adopted (not shot?) (empty? @errors))
        (let [intents @(:intents (nth ctxs adopted))]
          (when (seq intents)
            (let [[m x] (effect-mode frames)]
              (case m
                :defer (swap! (:intents x) into intents)
                (run-intents! intents adopted))))))
      (when-let [e (first @errors)]
        (fail (str "adoption failed, the fork was discarded: " (ex-message e)) (ex-data e))))))

;; ---------------------------------------------------------------------------
;; fork-resume: which captured authorities block a second resumption
;; ---------------------------------------------------------------------------

(defn resume-blocker
  "nil if authority t may be captured by a continuation resumed twice;
  else the reason."
  [t]
  (when-let [st (get-in @*store* [:tokens (auth-id t)])]
    (when (and (#{:open :advancing} (:status st)) (#{:resource :evidence} (:kind st)))
      (str "fork-resume: the continuation captured " (if (= :resource (:kind st)) "a resource" "an evidence")
           " authority, which cannot be split implicitly; it can be resumed only once"))))

;; ---------------------------------------------------------------------------
;; the operations (ambient :auth/*)
;; ---------------------------------------------------------------------------

(declare usable*)

(defn- validate-partition [systems parts]
  (let [described (set (keys systems))
        sets (mapv (comp set :systems) parts)
        freq (frequencies (mapcat seq sets))
        overlap (into (sorted-set) (keep (fn [[s n]] (when (> n 1) s))) freq)
        covered (set (keys freq))]
    (when (< (count parts) 2) (fail "partition! needs at least two parts"))
    (when (some #(or (not (set? (:systems %))) (empty? (:systems %))) parts)
      (fail "partition!: each part names a non-empty set of systems"))
    (when (some #(nil? (:owner %)) parts) (fail "partition!: each part needs an owner"))
    (when (seq overlap) (fail (str "partition!: parts overlap on " overlap)))
    (when-not (= covered described)
      (fail (str "partition!: parts must cover the systems exactly (unknown "
                 (into (sorted-set) (remove described covered)) ", omitted "
                 (into (sorted-set) (remove covered described)) ")")))))

(defn- world-of [x]
  (cond (instance? klara.world.World x) x
        (and (map? x) (instance? klara.world.World (:world x))) (:world x)
        :else (fail (str "branch!: a system must be a world or fiber, got " (pr-str x)))))

(defn op!
  "Perform authority operation op with args under frames. Machine-level
  operations (fork, adopt, direct, use) are in klara.eval."
  [op args frames]
  (let [chain (ctx-chain frames)
        [a b] args]
    (case op
      :auth/resource (mint! :resource a chain)
      :auth/capability (mint! :resource {:klara/capability a} chain)
      :auth/evidence (do (when-not (and (number? a) (not (neg? a)))
                           (fail "evidence needs a nonnegative mass"))
                         (swap! *store* update-in [:minted :evidence] + a)
                         (mint! :evidence {:mass a :spent 0 :moved 0} chain))
      :auth/budget (let [m (if (number? a) {:units a} a)
                         hard (cond (number? a) #{:units} (nil? b) #{} :else (set b))]
                     (when-not (and (map? m) (every? number? (vals m)))
                       (fail "budget needs a number or a map of components to numbers"))
                     (mint! :budget {:mass m :spent (czero m) :moved (czero m) :hard hard} chain))
      :auth/rand-key (let [k (mod (long a) M)] (mint! :randomness {:key (if (zero? k) 1 k)} chain))

      :auth/consume (let [st (usable a chain #{:resource} "consume!")]
                      (put! (:id st) (settled :consume nil))
                      (:payload st))
      :auth/payload (:payload (usable a chain #{:resource} "use!"))

      :auth/draw (let [st (usable a chain #{:randomness} "draw!")
                       k (next-key (get-in st [:payload :key]))]
                   (put! (:id st) #(assoc-in % [:payload :key] k))
                   (/ k M))

      :auth/spend
      (let [st (usable a chain #{:evidence :budget} "spend!")]
        (if (= :evidence (:kind st))
          (do (when-not (and (number? b) (not (neg? b))) (fail "spend!: evidence is spent by a nonnegative amount"))
              (when (> b (remaining* st))
                (fail (str "spend!: evidence overspent (" b " > " (remaining* st) " remaining)")))
              (put! (:id st) #(update-in % [:payload :spent] + b))
              b)
          (let [amt (if (number? b) {:units b} b)
                rem (c- (remaining* st) amt)
                hard (get-in st [:payload :hard])]
            (when-let [c (first (filter #(neg? (get rem % 0)) (sort hard)))]
              (fail (str "spend!: hard budget component " c " would be overspent")
                    {:component c}))
            (put! (:id st) #(update-in % [:payload :spent] c+ amt))
            rem)))

      :auth/remaining (remaining* (usable a chain #{:evidence :budget} "remaining"))

      :auth/split
      (let [st (usable a chain #{:evidence} "split")
            ws (cond (pos-int? b) (repeat b 1)
                     (and (sequential? b) (seq b) (every? #(and (number? %) (not (neg? %))) b)
                          (pos? (reduce + b))) b
                     :else (fail "split: give a positive count or a vector of weights"))
            s (reduce + ws)
            r (remaining* st)]
        (put! (:id st) #(-> % (update-in [:payload :moved] + r) (assoc :status :settled :operation :split)))
        (mapv #(mint! :evidence {:mass (n* r (/ % s)) :spent 0 :moved 0} chain {:origin :split}) ws))

      :auth/join
      (let [ts (vec a)
            sts (mapv #(usable % chain #{:evidence} "join") ts)]
        (when (empty? sts) (fail "join: needs at least one evidence authority"))
        (when-not (apply distinct? (map :id sts))
          (fail "join: the same evidence authority appears twice"))
        (let [r (reduce + (map remaining* sts))]
          (doseq [st sts]
            (put! (:id st) #(-> % (update-in [:payload :moved] + (remaining* st))
                                (assoc :status :settled :operation :join))))
          (mint! :evidence {:mass r :spent 0 :moved 0} chain {:origin :join})))

      :auth/branch
      (do (when-not (and (map? a) (seq a)) (fail "branch! takes a map of system ids to worlds"))
          (mint! :branchable
                 {:systems (into (sorted-map)
                                 (for [[sid x] a :let [p (world-of x) c (w/fork p)]]
                                   [sid {:parent p :child c :base (w/snapshot c)}]))}
                 chain))
      :auth/system (let [st (usable a chain #{:branchable} "system")]
                     (or (get-in st [:payload :systems b :child])
                         (fail (str "system: no system " b " in this authority"))))
      :auth/merge (do (usable* a chain :branchable "merge!") (merge-handle! (resolve-id (auth-id a) chain)))
      :auth/discard (do (usable* a chain :branchable "discard!") (discard-handle! (resolve-id (auth-id a) chain)))
      :auth/advance
      (let [st (usable a chain #{:branchable} "advance!")
            id (:id st)
            systems (get-in st [:payload :systems])]
        (run-op! id :advance
                 (fn []
                   (into (sorted-map)
                         (for [[sid {:keys [parent child base]}] systems
                               :let [cur (w/snapshot parent)
                                     mine (w/snapshot child)
                                     r (merge-roots base mine cur)]]
                           (do (conflict! sid r) [sid [cur mine r]]))))
                 (fn [plan]
                   (doseq [[sid [_ mine r]] plan]
                     (when *mutation-hook* (*mutation-hook* :advance sid))
                     (when-not (compare-and-set! (:root (get-in systems [sid :child])) mine r)
                       (fail (str "the branch of system " sid " changed during the advance"))))
                   {:advanced (vec (keys plan))})
                 (fn [s]
                   (-> s (assoc :status :open)
                       (dissoc :operation)
                       (update-in [:payload :systems]
                                  (fn [m] (into (sorted-map)
                                                (for [[sid sys] m]
                                                  [sid (assoc sys :base (w/snapshot (:parent sys)))]))))))))
      :auth/transfer
      (let [st (usable a chain #{:resource :evidence :budget :randomness :branchable} "transfer!")]
        (when (nil? b) (fail "transfer!: the new owner cannot be nil"))
        (let [t (mint! (:kind st) (:payload st) nil
                       {:scope (:scope st) :owner b :origin :transfer})]
          (when-let [c (some #(when (= (:id %) (:scope st)) %) chain)]
            (swap! (:owned c) conj (auth-id t)))
          (put! (:id st) #(cond-> (assoc % :status :settled :operation :transfer)
                            (= :evidence (:kind %))
                            (-> (assoc-in [:payload :moved] (get-in % [:payload :mass]))
                                (assoc-in [:payload :spent] 0))))
          t))
      :auth/partition
      (let [st (usable a chain #{:branchable} "partition!")
            systems (get-in st [:payload :systems])
            parts (vec b)]
        (validate-partition systems parts)
        (run-op! (:id st) :partition (constantly nil) (constantly nil)
                 (settled :partition nil))
        (mapv (fn [{:keys [systems owner]} ]
                (let [t (mint! :branchable {:systems (into (sorted-map) (select-keys (get-in st [:payload :systems]) systems))}
                               nil {:scope (:scope st) :owner owner :origin :partition})]
                  (when-let [c (some #(when (= (:id %) (:scope st)) %) chain)]
                    (swap! (:owned c) conj (auth-id t)))
                  t))
              parts))
      :auth/status
      (let [st (state (peek-id (token-id a "status") chain))]
        (cond-> {:kind (:kind st) :status (:status st)}
          (and (:operation st) (not= :open (:status st))) (assoc :operation (:operation st))
          (:owner st) (assoc :owner (:owner st))))
      :auth/receipts (receipts)
      (fail (str "no authority operation " op)))))

(defn- usable*
  "Check the kind of t under chain without requiring it to be open
  (merge! and discard! repeat idempotently on a settled authority)."
  [t chain kind what]
  (let [st (state (resolve-id (token-id t what) chain))]
    (when-not (= kind (:kind st))
      (fail (str what " needs a " (name kind) " authority, got " (name (:kind st)))))
    st))

(defn check-capability!
  "The resolved id of capability cap under frames (an open resource
  minted by `capability`)."
  [cap frames]
  (let [st (usable cap (ctx-chain frames) #{:resource} "direct")]
    (when-not (and (map? (:payload st)) (contains? (:payload st) :klara/capability))
      (fail "direct needs a capability (made by `capability`), not a plain resource"))
    (:id st)))

(defn direct-receipt!
  "Record an irreversible effect run directly under capability id; the
  capability must still be open."
  [cap-id sym args]
  (let [st (state cap-id)]
    (when-not (= :open (:status st))
      (fail (str "direct: capability is " (name (:status st)))))
    (receipt! {:kind :direct :capability cap-id :op sym :args (vec args)})))

;; ---------------------------------------------------------------------------
;; audits (tests)
;; ---------------------------------------------------------------------------

(defn evidence-held
  "Total evidence mass held by all tokens of the store (spent or
  remaining, not moved to another token)."
  []
  (reduce + 0 (for [[_ s] (:tokens @*store*) :when (= :evidence (:kind s))]
                (- (get-in s [:payload :mass]) (get-in s [:payload :moved])))))

(defn evidence-minted [] (get-in @*store* [:minted :evidence]))
