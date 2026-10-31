(ns klara.compile.check
  "The trusted checker (spec/L4-compiler.md#checking): decides whether a
  candidate term is equivalent to a reference term by definitional
  unfolding, the way a proof kernel compares terms.

  Both sides are put in weak head normal form by the meaning-preserving
  rewrites L4.check.beta, let-value, let-app, if-constant and prim. If the
  heads agree, subterms are compared; otherwise a definition at the head
  is unfolded (L4.check.delta), lazily and on one side at a time. Every
  step costs one unit of the job's budget. Unfolding a late link records
  the premise (name, generation) it relied on."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Closure]))

(defn- exhausted! [] (throw (ex-info "check exhausted" {::exhausted true})))

(defn- charge! [{:keys [^longs meter]}]
  (when meter
    (aset meter 0 (dec (aget meter 0)))
    (when (neg? (aget meter 0)) (exhausted!))))

;; ---------------------------------------------------------------------------
;; Values and constants

(defn- same-value?
  "Equality that also distinguishes number representations, so that folding
   never confuses 1 with 1N or 1.0."
  [a b]
  (cond
    (and (number? a) (number? b)) (and (= (class a) (class b)) (= a b))
    (and (sequential? a) (sequential? b)) (and (= (count a) (count b)) (every? true? (map same-value? a b)))
    (and (map? a) (map? b)) (and (= (count a) (count b))
                                 (every? (fn [[k x]] (and (contains? b k) (same-value? x (get b k)))) a))
    (or (v/closure? a) (v/code? a)) (identical? a b)
    :else (= a b)))

(defn- value-term?
  "A term whose evaluation cannot fail, diverge or perform an effect."
  [t]
  (contains? #{:const :local :fn :host} (:op t)))

(defn- data? [x]
  (not (or (fn? x) (v/closure? x) (instance? clojure.lang.IFn x) (v/mutable? x)
           (instance? clojure.lang.LazySeq x))))

(defn- fold-prim
  "L4.check.prim: a pure host function applied to constant data."
  [t]
  (let [f (:fn t) args (:args t)]
    (when (and (= :host (:op f))
               (= "clojure.core" (namespace (:name f)))
               (contains? b/pure-host (symbol (name (:name f))))
               (every? #(= :const (:op %)) args)
               (every? (comp data? :value) args))
      (try (let [r (apply @(resolve (:name f)) (map :value args))]
             (when (data? r) (t/const r)))
           (catch Throwable _ nil)))))

;; ---------------------------------------------------------------------------
;; Unfolding definitions (L4.check.delta)

(defn- closure-term
  "The term of closure `f` with its captured locals as constants and its
   globals linked by its basis."
  [^Closure f]
  (let [subst (into {} (map (fn [[n x]] [n (t/const (if (instance? clojure.lang.IDeref x) @x x))]))
                    (.-env f))
        term (t/substitute (.-term f) subst)]
    (if-let [basis (.-basis f)]
      ((requiring-resolve 'klara.runtime.intrinsics/pin-links) term basis)
      term)))

(defn- unfold
  "If `t` is a reference to a function definition, its term; else nil.
   Records a premise for late and guarded links."
  [ctx t]
  (case (:op t)
    :global (let [{:keys [kind name world generation]} (:link t)]
              (case kind
                :pinned (let [x (w/pin world name)]
                          (when (v/closure? x) (closure-term x)))
                (:late :guarded)
                (let [d (w/lookup (:world ctx) name)]
                  (when (and d (v/closure? (:value d))
                             (or (= kind :late) (= generation (:generation d))))
                    (vswap! (:premises ctx) conj [name (:generation d)])
                    (closure-term (:value d))))))
    :const (when (v/closure? (:value t)) (closure-term (:value t)))
    nil))

;; ---------------------------------------------------------------------------
;; Weak head normal form

(defn- beta
  "((fn [x..] b) e..) => (let [x e ..] b) (L4.check.let-app), when a fixed
   arity matches. Self references are replaced by the function itself."
  [f args]
  (when-let [a (first (filter #(and (nil? (:rest %)) (= (count args) (count (:params %)))) (:arities f)))]
    (let [[f a] (let [[f' m] (t/freshen f)]
                  [f' (first (filter #(and (nil? (:rest %)) (= (count args) (count (:params %)))) (:arities f')))])
          body (cond-> (:body a) (:self f) (t/substitute {(:self f) (dissoc f :self)}))]
      (reduce (fn [b [p e]] (t/let1 p e b)) body (reverse (map vector (:params a) args))))))

(defn whnf
  "Rewrite `t` at its head until no head rule applies."
  [ctx t]
  (charge! ctx)
  (case (:op t)
    :let (let [init (whnf ctx (:init t))]
           (if (value-term? init)                                ; L4.check.let-value
             (recur ctx (t/substitute (:body t) {(:name t) init}))
             (assoc t :init init)))
    :if (let [c (whnf ctx (:test t))]
          (if (= :const (:op c))                                 ; L4.check.if-constant
            (recur ctx (if (:value c) (:then t) (:else t)))
            (assoc t :test c)))
    :do (let [[x & more] (:body t)]
          (cond (empty? more) (recur ctx x)
                (value-term? (whnf ctx x)) (recur ctx (t/do* more))
                :else t))
    :recur (assoc t :args (mapv #(whnf ctx %) (:args t)))
    :app (let [f (whnf ctx (:fn t))
               args (mapv #(whnf ctx %) (:args t))
               t (assoc t :fn f :args args)]
           (cond
             (and (= :fn (:op f)) (not (:recur t)))
             (if-let [r (beta f args)] (recur ctx r) t)            ; L4.check.beta / let-app
             :else (or (some->> (fold-prim t) (whnf ctx)) t)))      ; L4.check.prim
    t))

;; ---------------------------------------------------------------------------
;; Comparison

(declare equal?)

(defn- unfold-head
  "Unfold the definition at the head of `t` (its function position for a
   call), or nil."
  [ctx t]
  (case (:op t)
    :app (when-let [f (unfold ctx (:fn t))] (assoc t :fn f))
    (unfold ctx t)))

(defn- bind-pairs
  "Rename binders of `b` to those of `a` (L4.check.alpha)."
  [b pairs]
  (t/rename b (into {} (map (fn [[x y]] [y x])) pairs)))

(defn- atomic? [t] (contains? #{:global :host :local :const} (:op t)))

(defn- same-shape [ctx a b]
  (case (:op a)
    :const (same-value? (:value a) (:value b))
    :local (= (:name a) (:name b))
    :host (= (:name a) (:name b))
    :global (= (:link a) (:link b))
    :app (and (= (count (:args a)) (count (:args b)))
              ;; atomic heads must match syntactically; otherwise the caller unfolds
              (let [fa (:fn a) fb (:fn b)]
                (if (and (atomic? fa) (atomic? fb))
                  (and (= (:op fa) (:op fb)) (same-shape ctx fa fb))
                  (equal? ctx fa fb)))
              (every? true? (map #(equal? ctx %1 %2) (:args a) (:args b))))
    :recur (and (= (:target a) (:target b)) (= (:arity a) (:arity b))
                (every? true? (map #(equal? ctx %1 %2) (:args a) (:args b))))
    :let (and (equal? ctx (:init a) (:init b))
              (equal? ctx (:body a) (bind-pairs (:body b) [[(:name a) (:name b)]])))
    :if (and (equal? ctx (:test a) (:test b)) (equal? ctx (:then a) (:then b)) (equal? ctx (:else a) (:else b)))
    :do (and (= (count (:body a)) (count (:body b))) (every? true? (map #(equal? ctx %1 %2) (:body a) (:body b))))
    :throw (equal? ctx (:ex a) (:ex b))
    :fn (and (= (count (:arities a)) (count (:arities b)))
             (every? true?
                     (map (fn [x y]
                            (and (= (count (:params x)) (count (:params y)))
                                 (= (nil? (:rest x)) (nil? (:rest y)))
                                 (let [pairs (cond-> (map vector (:params x) (:params y))
                                               (:rest x) (conj [(:rest x) (:rest y)])
                                               (and (:self a) (:self b)) (conj [(:self a) (:self b)]))]
                                   (equal? ctx (:body x) (bind-pairs (:body y) pairs)))))
                          (:arities a) (:arities b))))
    false))

(defn equal?
  "Is `a` equivalent to `b` under the checker's rules?"
  [ctx a b]
  (let [a (whnf ctx a) b (whnf ctx b)]
    (or (and (= (:op a) (:op b)) (same-shape ctx a b))
        (if-let [a' (unfold-head ctx a)]
          (equal? ctx a' b)
          (when-let [b' (unfold-head ctx b)]
            (equal? ctx a b')))
        (do (when-not @(:difference ctx) (vreset! (:difference ctx) [a b]))
            false))))

(defn check
  "Compare `reference` and `candidate` terms in preparation world `world`,
   charging `meter` (a long array, or nil). Returns
     {:result :equal :premises #{[q g] ..}}
     {:result :different :difference [ref-form cand-form]}
     {:result :exhausted}"
  [reference candidate world meter]
  (let [ctx {:world world :meter meter :premises (volatile! #{}) :difference (volatile! nil)}]
    (try
      (if (equal? ctx reference candidate)
        {:result :equal :premises @(:premises ctx)}
        {:result :different
         :difference (mapv t/->form @(:difference ctx))})
      (catch clojure.lang.ExceptionInfo e
        (if (::exhausted (ex-data e)) {:result :exhausted} (throw e))))))

;; ---------------------------------------------------------------------------
;; A normalizing recipe. It is NOT part of the trusted checker: its output
;; is checked like any other candidate. It unfolds a call when the callee is
;; a definition and some argument is a constant (online partial evaluation),
;; within a depth bound.

(defn- normalize* [ctx depth t]
  (let [t (whnf ctx t)
        go #(normalize* ctx depth %)]
    (case (:op t)
      :app (let [t (assoc t :fn (go (:fn t)) :args (mapv go (:args t)))]
             (if-let [u (and (pos? depth) (some #(= :const (:op %)) (:args t)) (unfold-head ctx t))]
               (normalize* ctx (dec depth) u)
               (or (some->> (fold-prim t) go) t)))
      :fn (t/fn-term (:self t) (mapv #(update % :body go) (:arities t)))
      :let (let [t (assoc t :init (go (:init t)) :body (go (:body t)))]
             (if (value-term? (:init t)) (go (t/substitute (:body t) {(:name t) (:init t)})) t))
      :if (let [c (go (:test t))]
            (if (= :const (:op c)) (go (if (:value c) (:then t) (:else t)))
                (assoc t :test c :then (go (:then t)) :else (go (:else t)))))
      :do (t/do* (mapv go (:body t)))
      :recur (assoc t :args (mapv go (:args t)))
      t)))

(defn normalize
  "Normalize `term` in `world`, charging `meter`. Returns the term, or nil
   if the budget ran out."
  [term world meter & {:keys [depth] :or {depth 64}}]
  (let [ctx {:world world :meter meter :premises (volatile! #{}) :difference (volatile! nil)}]
    (try (t/refresh-free (normalize* ctx depth term))
         (catch clojure.lang.ExceptionInfo e
           (if (::exhausted (ex-data e)) nil (throw e))))))
