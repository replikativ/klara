(ns klara.compile.affine
  "The declared affine subset (design/04-ownership.md#the-judgment,
  design/10-accounting.md, L4.check.affine).

  `(defaffine f [^:own t ^:borrow b x] body)` defines `f` like `defn` after
  checking, when it is defined, that the tokens in its body are threaded:
  owned collections (`own`, `conj!`, ..., `persistent!`) and account tokens
  (`klara.account/take`, `spend`, `split`, `join`, `put`). The clauses, as
  numbered in the diagnostics:

    1. a token is made by `own` or `take`, by an operation on a token, by a
       declared call that returns one, or is an `^:own` parameter; the
       operations that consume a token are given one;
    2. each token is consumed at most once on every path; reads come before
       its consumption;
    3. both arms of a branch consume the same tokens and give the same kind
       of result; a loop threads its tokens through `recur`;
    4. a token is never captured by a function, stored in data, passed to
       a function other than an operation or a declared definition at an
       `^:own` or `^:borrow` position, or used anywhere else; a borrowed
       parameter is only read or passed on as a borrow;
    5. a call of a declared definition consumes the tokens at its `^:own`
       positions and gives back what it declares it returns;
    6. at every exit each token was consumed or is returned (alone, or in a
       vector), and no token is dropped;
    7. no token is live where the computation may be captured: at a
       `perform`, a `def`, or a call that may perform (L4.facts.effect above
       `:shared`, a function it cannot see, a definition that does). A
       continuation is multi-shot, and authority is not (L3.cont.context).

  `try` (clause 4): the body may read the tokens live before it and consume
  them; those it may consume are unavailable after the `try` on both paths
  (on the handler path the raise point is unknown, and a token the body did
  not reach stays live until its job settles). The `try` gives no token;
  catch and finally arms read only the tokens the body leaves live.

  Tokens that reach the definition from code it does not judge (the result
  of an undeclared call, `run`, interop) are data to the judgment: it cannot
  operate on them (clause 1), so their dynamic checks remain.

  The definition is compiled when it is made (L4.check.affine-erase): the
  kernel checks the definition as its own candidate and installs it. The
  compiled code calls the account operations on the context's wallet with
  their checks (in this representation the lookup that finds a token's
  amount is the reuse check); a definition the backend cannot compile runs
  interpreted. Its use is the diagnostic at
  definition, naming the clause and the place, and the declaration
  `:klara/affine {:own #{i} :borrow #{i} :returns r}` that callers are
  checked against."
  (:require [klara.lang.builtins :as b]
            [klara.compile.facts :as facts]
            [klara.lang.expand :as ex]
            [klara.lang.term :as t]))

(def ^:private ^:dynamic *place* "The nearest enclosing source position." nil)

(def ^:private ^:dynamic *self*
  "The definition being checked: its name and whether its body may be captured."
  nil)

(def ^:private ^:dynamic *premises*
  "The effect facts the judgment relied on: [q generation] pairs (a volatile)."
  nil)

(defn- violation [clause term msg & [local]]
  (throw (ex-info (str "defaffine: " msg (when local (str ": " (t/base-name local))))
                  {:rule :L4.check.affine :clause clause :place (or (:pos term) *place*)
                   :local (some-> local t/base-name)})))

(def ^:private ops
  "Operations on tokens: the argument positions they consume or read, and
   what they return (:token, :value or {:tuple positions})."
  (merge
   (zipmap '[klara.core/conj! klara.core/assoc! klara.core/dissoc! klara.core/disj! klara.core/pop!
             klara.account/spend]
           (repeat {:consumes #{0} :returns :token}))
   (zipmap '[clojure.core/get clojure.core/count clojure.core/contains? clojure.core/nth
             klara.account/holds? klara.account/balance]
           (repeat {:reads #{0} :returns :value}))
   '{klara.core/own {:returns :token}
     klara.account/take {:returns :token}
     klara.core/persistent! {:consumes #{0} :returns :value}
     klara.account/put {:consumes #{0} :returns :value}
     klara.account/split {:consumes #{0} :returns {:tuple #{0 1}}}
     klara.account/join {:consumes #{0 1} :returns :token}}))

;; The state: :live maps a local to :token, :borrow or {:tuple S :taken T}
;; (a pair whose token positions S are taken apart with nth; it owes the
;; positions not in T); :dead holds the locals an operation consumed.

(defn- token-result? [k] (or (= :token k) (map? k)))

(defn- owes? [k] (or (= :token k) (and (map? k) (not= (:tuple k) (:taken k)))))

(defn- live-tokens [st]
  (into #{} (keep (fn [[n k]] (when (owes? k) n))) (:live st)))

(defn- consume [st n term]
  (cond (contains? (:dead st) n) (violation 2 term "a token used after an operation consumed it" n)
        (= :borrow (get-in st [:live n])) (violation 4 term "a borrowed value cannot be consumed or returned" n)
        :else (-> st (update :live dissoc n) (update :dead conj n))))

(defn- spec-of [env f]
  (case (:op f)
    :host (get ops (:name f))
    :global (when-let [d ((:defined env) (get-in f [:link :name]))]
              (when-let [a (get-in d [:meta :klara/affine])]
                {:consumes (:own a) :reads (:borrow a) :returns (or (:returns a) :value) :declared true}))
    nil))

(def ^:private uncapturing-intrinsics
  "Intrinsics that never capture the caller's continuation: account
   operations, and jobs (a job frame stops effect search, L3.job.run)."
  '#{klara.job/run klara.job/run-all klara.job/resume})

(declare capture-points)

(defn- capture
  "Why calling `f` (the operator of an application) may capture the
   caller's continuation (clause 7), or nil. Host functions cannot: a Klara
   callback they call runs in a nested machine (L3.effect.host-boundary)."
  [env f]
  (case (:op f)
    :host (let [q (:name f)]
            (when (and (= :intrinsic (:kind (b/lookup q)))
                       (not (contains? ops q))
                       (not= "klara.account" (namespace q))
                       (not (contains? uncapturing-intrinsics q))
                       (not (#{:pure :fresh} (facts/intrinsic-class q))))
              (str "calls " q)))
    :global (let [q (get-in f [:link :name])]
              (if (= q (:name *self*))
                (when @(:captures *self*) (str "calls itself, and its body " @(:captures *self*)))
                (when-let [d ((:defined env) q)]
                  (when (instance? klara.runtime.value.Closure (:value d))
                    (let [e (facts/effect (:world env) q)]
                      (when *premises* (vswap! *premises* into (:premises e)))
                      (cond (not (#{:pure :fresh :shared} (:class e)))
                            (str "calls " (t/base-name q) ", which may perform (" (:why e) ")")
                            (seq (:relative e))
                            (str "calls " (t/base-name q) ", whose effect is its arguments'")))))))
    :fn nil                                                ; its body is checked in place
    (str "calls a function it cannot see")))

(defn- capture-points
  "The first place in `term` where the computation may be captured, as a
   reason, or nil (for a definition calling itself)."
  [env term]
  (or (case (:op term)
        :def (str "defines " (:name term))
        :app (capture env (:fn term))
        nil)
      (some #(capture-points env %) (t/children term))))

(defn- capturable!
  "Clause 7: refuse a capture point while a token (owned, borrowed or in a
   pair) is live."
  [st term reason]
  (when (and reason (seq (:live st)))
    (violation 7 term (str "a token is live where the computation may be captured: " reason)
               (first (keys (:live st))))))

(declare chk)

(defn- move
  "Check `term` where a token may be moved: a token local is consumed and
   its kind is the result."
  [st term env ctx]
  (if (= :local (:op term))
    (let [n (:name term) k (get-in st [:live n])]
      (cond (contains? (:dead st) n) (violation 2 term "a token used after an operation consumed it" n)
            (= :token k) [(consume st n term) :token]
            (map? k) (violation 4 term "a pair of tokens must be taken apart with nth" n)
            :else (chk st term env ctx false)))
    (chk st term env ctx false)))

(defn- value [st term env ctx]
  (let [[st k] (chk st term env ctx false)]
    (when (token-result? k) (violation 4 term "a token passed where it would be lost or copied"))
    st))

(defn- op-app [st term spec env ctx]
  (let [{:keys [consumes reads returns]} spec
        ;; arguments are evaluated before the operation consumes its tokens,
        ;; so reads in later arguments come before the consumption
        [st deferred]
        (reduce (fn [[st deferred] [i a]]
                  (cond
                    (contains? consumes i)
                    (if (and (= :local (:op a)) (= :token (get-in st [:live (:name a)])))
                      [st (conj deferred a)]
                      (let [[st k] (move st a env ctx)]
                        (when-not (= :token k)
                          (violation 1 a (str (t/->form (:fn term)) " needs a token here")))
                        [st deferred]))

                    (and (contains? reads i) (= :local (:op a)) (contains? (:live st) (:name a)))
                    (do (when (map? (get-in st [:live (:name a)]))
                          (violation 4 a "a pair of tokens must be taken apart with nth" (:name a)))
                        [st deferred])

                    (and (contains? reads i) (= :local (:op a)) (contains? (:dead st) (:name a)))
                    (violation 2 a "a token read after an operation consumed it" (:name a))

                    :else [(value st a env ctx) deferred]))
                [st []] (map-indexed vector (:args term)))]
    [(reduce (fn [st a] (consume st (:name a) a)) st deferred) returns]))

(defn- nth-of-tuple [st term]
  (let [[p i] (:args term) n (:name p) k (get-in st [:live n])]
    (when (and (= :local (:op p)) (map? k) (= :const (:op i)))
      (let [j (:value i)]
        (cond (not (contains? (:tuple k) j)) [st :value]
              (contains? (:taken k) j) (violation 2 term "a token taken out of a pair twice" n)
              :else (let [taken (conj (:taken k) j)]
                      [(assoc-in st [:live n :taken] taken) :token]))))))

(defn- merge-kind [term a b]
  (cond (= :recur a) b
        (= :recur b) a
        (= a b) a
        :else (violation 3 term "the branches give different kinds of result")))

(defn- loop-app [st term env ctx tail?]
  (let [f (:fn term)
        {:keys [params body]} (first (:arities f))
        [st kinds] (reduce (fn [[st ks] a] (let [[st k] (move st a env ctx)] [st (conj ks k)])) [st []] (:args term))
        outer (:live st)
        ;; tokens from outside the loop are read-only inside it
        inner (merge (update-vals outer (constantly :borrow))
                     (into {} (keep (fn [[p k]] (when (token-result? k) [p k]))) (map vector params kinds)))
        positions (set (keep-indexed (fn [j k] (when (token-result? k) j)) kinds))
        [st' k] (chk (assoc st :live inner) body env {:self (:self f) :positions positions :outer (set (keys outer))} true)
        left (remove (set (keys outer)) (live-tokens st'))]
    (when (seq left) (violation 6 term "a loop leaves a token neither consumed nor returned" (first left)))
    ;; outer tokens were only read inside: they are live after the loop as before
    [(assoc st' :live outer) (if (= :recur k) :value k)]))

(defn- tail-vector [st term env ctx]
  (let [[st ks] (reduce (fn [[st ks] a] (let [[st k] (move st a env ctx)] [st (conj ks k)])) [st []] (:args term))
        positions (set (keep-indexed (fn [j k] (when (= :token k) j)) ks))]
    [st (if (seq positions) {:tuple positions} :value)]))

(declare chk*)

(defn- chk
  "Check `term` in state `st`; returns [state kind]."
  [st term env ctx tail?]
  (binding [*place* (or (:pos term) *place*)] (chk* st term env ctx tail?)))

(declare chk-app chk-try chk-other)

(defn- chk*
  [st term env ctx tail?]
  (case (:op term)
    :const [st :value]
    :local (let [n (:name term) k (get-in st [:live n])]
             (cond (contains? (:dead st) n) (violation 2 term "a token used after an operation consumed it" n)
                   (and tail? (= :token k)) [(consume st n term) :token]
                   k (violation 4 term (if (= :borrow k) "a borrowed value used other than by reading it"
                                           "a token used other than by an operation") n)
                   :else [st :value]))
    :let (let [[st k] (move st (:init term) env ctx)
               n (:name term)
               st (cond-> st (token-result? k) (assoc-in [:live n] (if (map? k) (assoc k :taken #{}) k)))
               [st k2] (chk st (:body term) env ctx tail?)]
           (when (owes? (get-in st [:live n]))
             (violation 6 term "a token is dropped: consume it, put it back or return it" n))
           [st k2])
    :if (let [st (value st (:test term) env ctx)
              [a ka] (chk st (:then term) env ctx tail?)
              [b kb] (chk st (:else term) env ctx tail?)]
          (when-not (= (set (live-tokens a)) (set (live-tokens b)))
            (violation 3 term "the branches consume different tokens"))
          [(assoc a :dead (into (:dead a) (:dead b))) (merge-kind term ka kb)])
    :do (let [stmts (butlast (:body term))
              st (reduce (fn [st s]
                           (let [[st k] (chk st s env ctx false)]
                             (when (token-result? k)
                               (violation 6 s "a token is dropped: its result is not used"))
                             st))
                         st stmts)]
          (chk st (last (:body term)) env ctx tail?))
    :recur (let [{:keys [self positions outer]} ctx]
             (when-not (and self (= self (:target term)))
               (violation 3 term "recur outside the loop it threads"))
             (let [[st ks] (reduce (fn [[st ks] [j a]]
                                     (if (contains? positions j)
                                       (let [[st k] (move st a env ctx)]
                                         (when-not (= :token k)
                                           (violation 3 a "recur must pass the next token at a token's position"))
                                         [st (conj ks k)])
                                       [(value st a env ctx) (conj ks :value)]))
                                   [st []] (map-indexed vector (:args term)))
                   left (remove outer (live-tokens st))]
               (when (seq left) (violation 6 term "a token is neither consumed nor passed to recur" (first left)))
               [st :recur]))
    :fn (let [captured (filter #(or (contains? (:live st) %) (contains? (:dead st) %)) (t/free-locals term))]
          (when (seq captured) (violation 4 term "a token captured by a function" (first captured)))
          (doseq [{:keys [params body]} (:arities term)]
            (chk {:live {} :dead #{}} body env {} true))
          [st :value])
    :app (let [f (:fn term)
               spec (spec-of env f)
               [st' k :as r] (chk-app st term f spec env ctx tail?)]
           ;; the tokens still live during the call (those moved into it are the callee's)
           (capturable! st' term (capture env f))
           r)
    :try (chk-try st term env ctx)
    :def (do (capturable! st term (str "defines " (:name term)))
             (chk-other st term env ctx))
    (chk-other st term env ctx)))

(defn- chk-app [st term f spec env ctx tail?]
           (cond
             (and (= :host (:op f)) (= 'clojure.core/nth (:name f)) (nth-of-tuple st term))
             (nth-of-tuple st term)

             spec (op-app st term spec env ctx)

             (and (= :fn (:op f)) (:self f) (= 1 (count (:arities f)))
                  (= (count (:args term)) (count (:params (first (:arities f))))))
             (loop-app st term env ctx tail?)

             (and tail? (= :host (:op f)) (= 'clojure.core/vector (:name f)))
             (tail-vector st term env ctx)

             :else (let [st (value st f env ctx)]
                     [(reduce (fn [st a] (value st a env ctx)) st (:args term)) :value])))

(defn- chk-other
  "Any other form (throw, def, interop, letrec, code, ...): it may not
   mention a token, and none of its parts may give one (a token made inside
   would be stored, thrown or quoted)."
  [st term env ctx]
  (let [used (filter #(or (contains? (:live st) %) (contains? (:dead st) %)) (t/free-locals term))]
    (when (seq used) (violation 4 term "a token used other than by an operation" (first used)))
    (doseq [c (t/children term)] (value st c env ctx))
    [st :value]))

(defn- chk-try
  "try (clause 4): see the namespace docstring."
  [st term env ctx]
  (let [[st1 k] (chk st (:body term) env ctx false)
        _ (when (token-result? k)
            (violation 4 term "a try gives no token: consume or put it back inside the body"))
        live (set (live-tokens st1))
        arm (fn [acc b]
              (let [[sa ka] (chk st1 b env ctx false)]
                (when (token-result? ka) (violation 4 b "a catch or finally gives no token"))
                (when-not (= live (set (live-tokens sa)))
                  (violation 3 b "a catch or finally may only read the tokens the body leaves live"))
                (update acc :dead into (:dead sa))))
        arms (concat (map :body (:catches term)) (when (:finally term) [(:finally term)]))]
    [(reduce arm st1 arms) :value]))

(declare check*)

(defn check
  "Check a declared definition's fn term; returns what it returns (:value,
   :token or {:tuple positions}). `self` is the definition's qualified name."
  ([fn-term own borrow env] (check fn-term own borrow env nil))
  ([fn-term own borrow env self]
   (binding [*self* {:name self :captures (delay (capture-points env fn-term))}]
     (check* fn-term own borrow env))))

(defn- check* [fn-term own borrow env]
  (let [{:keys [params rest body]} (first (:arities fn-term))]
    (when (or rest (not= 1 (count (:arities fn-term))))
      (violation 1 fn-term "defaffine takes one fixed parameter vector"))
    (let [live (into {} (concat (map (fn [i] [(nth params i) :token]) own)
                                (map (fn [i] [(nth params i) :borrow]) borrow)))
          [st k] (binding [*place* (:pos fn-term)] (chk {:live live :dead #{}} body env {} true))
          left (live-tokens st)]
      (when (seq left) (violation 6 fn-term "a token is neither consumed nor returned" (first left)))
      (if (= :recur k) :value k))))

(defn- positions [params flag] (set (keep-indexed (fn [i p] (when (get (meta p) flag) i)) params)))

(b/register! 'klara.core/defaffine                                   ; L4.check.affine
  {:kind :macro
   :fn (fn [form env]
         (let [[_ nm & more] form
               [doc more] (if (string? (first more)) [(first more) (rest more)] [nil more])
               [params & body] more
               _ (when-not (vector? params)
                   (throw (ex-info "defaffine takes one parameter vector"
                                   {:rule :L4.check.affine :clause 1})))
               own (positions params :own)
               borrow (positions params :borrow)
               ;; the definition's position, for diagnostics on forms that have none
               fn-form (with-meta (list* 'clojure.core/fn params body) (meta form))
               self (symbol (str (:ns env)) (name nm))
               term (ex/expand (assoc env :self self) fn-form)
               premises (volatile! #{})
               returns (binding [*premises* premises] (check term own borrow env self))]
           ;; L4.check.affine-erase: compiled when it is defined, as it is (the
           ;; kernel checks the candidate against the definition and installs it)
           (list 'do
                 (list* 'def (vary-meta nm assoc :klara/affine {:own own :borrow borrow :returns returns
                                                                :premises @premises})
                        (concat (when doc [doc]) [fn-form]))
                 (list 'let ['outcome__affine (list 'klara.compiler.kernel/prepare
                                                    (list 'klara.compiler.kernel/reference (list 'quote self))
                                                    {:name (list 'quote self)})]
                       (list 'if (list '= :ready (list :status 'outcome__affine))
                             (list 'klara.compiler.kernel/install! 'outcome__affine)
                             nil)
                       (list 'quote self)))))})
