(ns klara.compile.check
  "The trusted checker (spec/L4-compiler.md#checking): decides whether a
  candidate term is equivalent to a reference term by definitional
  unfolding, the way a proof kernel compares terms.

  Both sides are put in weak head normal form by the meaning-preserving
  rewrites L4.check.beta, let-value, let-app, if-constant and prim. If the
  heads agree, subterms are compared; otherwise a definition at the head
  is unfolded (L4.check.delta), lazily and on one side at a time. Every
  step costs one unit of the job's budget. Unfolding a late link records
  the premise (name, generation) it relied on.

  The definition being prepared (the `self` of a check) is never unfolded on
  the candidate's side (L4.check.self): after installation its name means
  the candidate, so treating it as its reference there would assume what is
  being shown. Unfolding it on the reference's side is a finite unfolding of
  the reference, which has the same fixed point."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.prims :as prims]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Closure]))

(set! *warn-on-reflection* true)

(defn- exhausted! [] (throw (ex-info "check exhausted" {::exhausted true})))

(defn- charge! [{:keys [^longs meter]}]
  (when meter
    (aset meter 0 (dec (aget meter 0)))
    (when (neg? (aget meter 0)) (exhausted!))))

;; ---------------------------------------------------------------------------
;; Values and constants

(defn- same-value?
  "Constants that no Klara program can tell apart: the same class, the same
   metadata, and for collections the same elements in the same iteration
   order (so 1 and 1N, a list and a vector, an array map and a hash map, a
   sorted and a hash set all differ). Functions, code and other objects are
   compared by identity; lazy sequences too, since comparing them would run
   them."
  [a b]
  (cond
    (identical? a b) true
    (not= (class a) (class b)) false
    (not (same-value? (meta a) (meta b))) false
    (instance? clojure.lang.LazySeq a) false
    (or (map? a) (set? a) (sequential? a))
    (and (= (count a) (count b))
         (every? true? (map same-value? (seq a) (seq b))))
    (instance? java.util.Map$Entry a) (and (same-value? (key a) (key b)) (same-value? (val a) (val b)))
    (or (nil? a) (number? a) (string? a) (keyword? a) (symbol? a) (boolean? a) (char? a)) (= a b)
    :else false))

(defn- value-sig
  "A value's identity for keys: its class, metadata and structure."
  [x]
  (cond (nil? x) nil
        (or (map? x) (set? x) (sequential? x))
        (if (instance? clojure.lang.LazySeq x)
          [::object (System/identityHashCode x)]
          [(class x) (value-sig (meta x)) (mapv value-sig (seq x))])
        (instance? java.util.Map$Entry x) [(value-sig (key x)) (value-sig (val x))]
        (or (number? x) (string? x) (keyword? x) (symbol? x) (boolean? x) (char? x))
        [(class x) (when (instance? clojure.lang.IMeta x) (value-sig (meta x))) x]
        :else [::object (System/identityHashCode x)]))

(defn- value-term?
  "A term whose evaluation cannot fail, diverge or perform an effect."
  [t]
  (contains? #{:const :local :fn :host} (:op t)))

(def data? "Immutable data the checker may compute with (klara.runtime.value/data?)." v/data?)

(defn- fold-prim
  "L4.check.prim: a pure host function applied to constant data."
  [t]
  (let [f (:fn t) args (:args t)]
    (when (and (= :host (:op f))
               (or (and (= "clojure.core" (namespace (:name f)))
                        (contains? b/pure-host (symbol (name (:name f)))))
                   (:pure (b/lookup (:name f))))
               (every? #(= :const (:op %)) args)
               (every? (comp data? :value) args))
      (try (let [hf (if-let [e (b/lookup (:name f))] (:fn e) @(resolve (:name f)))
                 r (apply hf (map :value args))]
             (when (data? r) (t/const r)))
           (catch Throwable _ nil)))))

;; ---------------------------------------------------------------------------
;; Unfolding definitions (L4.check.delta)

(defn- closure-term
  "The term of closure `f` with its captured locals as constants and its
   globals linked by its basis."
  [^Closure f]
  (let [subst (into {} (map (fn [[n x]] [n (t/const (if (instance? clojure.lang.IDeref x) @x x))]))
                    (v/captured f))
        term (t/substitute (.-term f) subst)]
    (if-let [basis (.-basis f)]
      ((requiring-resolve 'klara.runtime.intrinsics/pin-links) term basis)
      term)))

(defn- unfold
  "If `t` is a reference to a function definition, its term; else nil.
   Records a premise for late and guarded links. On the candidate's side the
   definition being prepared is not unfolded (L4.check.self)."
  [ctx t side]
  (case (:op t)
    :global (let [{:keys [kind name world generation]} (:link t)]
              (if (and (= side :candidate) (some? (:self ctx)) (= name (:self ctx)))
                nil
              (case kind
                :pinned (let [x (w/pin world name)]
                          (when (v/closure? x) (closure-term x)))
                (:late :guarded)
                (let [d (w/lookup (:world ctx) name)]
                  (when (and d (v/closure? (:value d))
                             (or (= kind :late) (= generation (:generation d))))
                    (vswap! (:premises ctx) conj [name (:generation d)])
                    (closure-term (:value d)))))))
    :const (when (v/closure? (:value t)) (closure-term (:value t)))
    nil))

;; Data definitions (L4.check.delta-data): a global whose definition is
;; immutable data means that data, with its generation as a premise.

(defn- data-definition
  "The value of global term `t` if it is defined as immutable data, as [v]."
  [ctx t]
  (let [{:keys [kind name world generation]} (:link t)]
    (case kind
      :pinned (let [x (w/pin world name)]
                (when (and (not (v/closure? x)) (data? x)) [x]))
      (:late :guarded)
      (let [d (w/lookup (:world ctx) name)
            x (:value d)]
        (when (and d (not (:macro? d)) (not (v/closure? x)) (data? x)
                   (or (= kind :late) (= generation (:generation d))))
          (vswap! (:premises ctx) conj [name (:generation d)])
          [x]))
      nil)))

;; ---------------------------------------------------------------------------
;; Weak head normal form

(defn- beta
  "((fn [x..] b) e..) => (let [x e ..] b) (L4.check.let-app), when a fixed
   arity matches. Self references are replaced by the function itself."
  [f args]
  (when-let [a (first (filter #(and (nil? (:rest %)) (= (count args) (count (:params %)))
                                    ;; a loop is not unrolled: its recur needs the function
                                    (not-any? (fn [n] (and (= :recur (:op n)) (= (:self f) (:target n))))
                                              (t/nodes (:body %))))
                              (:arities f)))]
    (let [[f a] (let [[f' m] (t/freshen f)]
                  [f' (first (filter #(and (nil? (:rest %)) (= (count args) (count (:params %)))) (:arities f')))])
          body (cond-> (:body a) (:self f) (t/substitute {(:self f) (dissoc f :self)}))]
      (reduce (fn [b [p e]] (t/let1 p e b)) body (reverse (map vector (:params a) args))))))

(defn- signed
  "`t` with every constant replaced by its value's signature."
  [t]
  (let [cs (t/children t)
        t (if (seq cs) (t/with-children t (mapv signed cs)) t)]
    (if (= :const (:op t)) (assoc t :value (value-sig (:value t))) t)))

(defn- term-key
  "Assumption key: terms that differ only in how their constants print
   (1 and 1N, a list and a vector) get different keys."
  [t]
  (t/->form (signed t)))

(defn- assumed
  "true or false if the truth of `t` is assumed in `ctx`, else nil."
  [ctx t]
  (get (:assume ctx) (term-key t)))

(defn- assume
  "ctx in which guard `g` is known truthy (and the test it negates falsy)."
  [ctx g]
  (let [ctx (assoc-in ctx [:assume (term-key g)] true)]
    (if (and (= :app (:op g)) (= 'clojure.core/not (get-in g [:fn :name])) (= 1 (count (:args g))))
      (assoc-in ctx [:assume (term-key (first (:args g)))] false)
      ctx)))

(defn whnf
  "Rewrite `t` at its head until no head rule applies."
  [ctx t]
  (charge! ctx)
  (case (:op t)
    :let (let [init (whnf ctx (:init t))]
           (if (value-term? init)                                ; L4.check.let-value
             (recur ctx (t/substitute (:body t) {(:name t) init}))
             (assoc t :init init)))
    :if (let [c (whnf ctx (:test t))
              known (assumed ctx c)]
          (cond (= :const (:op c))                               ; L4.check.if-constant
                (recur ctx (if (:value c) (:then t) (:else t)))
                (some? known)                                    ; L4.check.speculate-assume
                (recur ctx (if known (:then t) (:else t)))
                :else (assoc t :test c)))
    :do (let [[x & more] (:body t)]
          (cond (empty? more) (recur ctx x)
                (value-term? (whnf ctx x)) (recur ctx (t/do* more))
                :else t))
    :recur (assoc t :args (mapv #(whnf ctx %) (:args t)))
    :global (if-let [[x] (data-definition ctx t)] (t/const x) t)      ; L4.check.delta-data
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
   call), or nil. `side` is :reference or :candidate."
  [ctx t side]
  (case (:op t)
    :app (when-let [f (unfold ctx (:fn t) side)] (assoc t :fn f))
    ;; the term evaluated first: a definition there may be unfolded too
    ;; (unfolding is a congruence; L4.check.delta)
    :let (when-let [i (unfold-head ctx (:init t) side)] (assoc t :init i))
    :if (when-let [c (unfold-head ctx (:test t) side)] (assoc t :test c))
    (unfold ctx t side)))

(defn- bind-pairs
  "Rename binders of `b` to those of `a` (L4.check.alpha)."
  [b pairs]
  (t/rename b (into {} (map (fn [[x y]] [y x])) pairs)))

(defn- ordered-binders
  "Locals bound by `t` itself, in the order they occur (for pairing)."
  [t]
  (case (:op t)
    :fn (cond->> (vec (mapcat (fn [a] (cond-> (vec (:params a)) (:rest a) (conj (:rest a)))) (:arities t)))
          (:self t) (into [(:self t)]))
    :let [(:name t)]
    :letrec (mapv first (:bindings t))
    :try (mapv :name (:catches t))
    []))

(defn- template-binders [tmpl] (vec (mapcat ordered-binders (t/nodes tmpl))))

(defn- canonical-template
  "The template of code term `id`, with its own binders and code ids renamed
   by position, profiles dropped and constants signed: two templates are the
   same syntax up to the names they bind iff these are equal (L4.check.code)."
  [id tmpl]
  (let [ns (t/nodes tmpl)
        bm (zipmap (template-binders tmpl) (map #(symbol (str "b" %)) (range)))
        im (zipmap (into [id] (keep #(when (= :code (:op %)) (:id %))) ns) (map #(symbol (str "c" %)) (range)))
        relabel (fn relabel [t]
                  (let [cs (t/children t)
                        t (cond-> (dissoc t :profile) (seq cs) (t/with-children (mapv relabel cs)))]
                    (case (:op t)
                      :code (update t :id im)
                      :hole (update t :code im)
                      t)))]
    (signed (t/refresh-free (relabel (t/rename tmpl bm))))))

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
    :try (and (equal? ctx (:body a) (:body b))
              (= (count (:catches a)) (count (:catches b)))
              (every? true? (map (fn [x y]
                                   (and (= (:class x) (:class y))
                                        (equal? ctx (:body x) (bind-pairs (:body y) [[(:name x) (:name y)]]))))
                                 (:catches a) (:catches b)))
              (= (nil? (:finally a)) (nil? (:finally b)))
              (or (nil? (:finally a)) (equal? ctx (:finally a) (:finally b))))
    :letrec (and (= (count (:bindings a)) (count (:bindings b)))
                 (let [b (bind-pairs b (map (fn [[x] [y]] [x y]) (:bindings a) (:bindings b)))]
                   (and (every? true? (map (fn [[_ i] [_ j]] (equal? ctx i j)) (:bindings a) (:bindings b)))
                        (equal? ctx (:body a) (:body b)))))
    :def (and (= (select-keys a [:name :macro? :meta :doc]) (select-keys b [:name :macro? :meta :doc]))
              (equal? ctx (:init a) (:init b)))
    ;; L4.check.code: a template is a value, compared as syntax; its holes are
    ;; terms evaluated in order, which see the template's binders
    :code (and (= (count (:holes a)) (count (:holes b)))
               (= (canonical-template (:id a) (:template a)) (canonical-template (:id b) (:template b)))
               (let [pairs (map vector (template-binders (:template a)) (template-binders (:template b)))]
                 (every? true? (map #(equal? ctx %1 (bind-pairs %2 pairs)) (:holes a) (:holes b)))))
    :interop (and (= (select-keys a [:static? :new? :target :member]) (select-keys b [:static? :new? :target :member]))
                  (= (count (t/children a)) (count (t/children b)))
                  (every? true? (map #(equal? ctx %1 %2) (t/children a) (t/children b))))
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

(def ^:private total-predicates
  "Pure host functions that return for every argument."
  '#{clojure.core/number? clojure.core/integer? clojure.core/int? clojure.core/double?
     clojure.core/float? clojure.core/string? clojure.core/keyword? clojure.core/symbol?
     clojure.core/map? clojure.core/vector? clojure.core/seq? clojure.core/coll?
     clojure.core/fn? clojure.core/boolean? clojure.core/set? clojure.core/nil?
     clojure.core/some? clojure.core/true? clojure.core/false? clojure.core/not
     clojure.core/identical?})
;; = and not= are not here: comparing a lazy sequence realizes it, which runs
;; Klara code that may fail or not terminate.

(defn- same-guard?
  "Is host term f the value-speculation guard? Recognized by the function it
   names (klara.runtime.prims/same?), not by a library's name for it."
  [f]
  (and (= :host (:op f)) (identical? (:fn (b/lookup (:name f))) prims/same?)))

(defn- class-test?
  "(instance? C x) with C a constant class: total (with any other first
   argument instance? throws)."
  [t]
  (and (= :app (:op t))
       (= :host (get-in t [:fn :op]))
       (= 'clojure.core/instance? (get-in t [:fn :name]))
       (= 2 (count (:args t)))
       (= :const (:op (first (:args t))))
       (class? (:value (first (:args t))))))

(defn- total-guard?
  "Locals and constants, and total predicates applied to total guards."
  [t]
  (or (contains? #{:local :const} (:op t))
      (and (= :app (:op t))
           (= :host (get-in t [:fn :op]))
           (or (contains? total-predicates (get-in t [:fn :name])) (same-guard? (:fn t)) (class-test? t))
           (every? total-guard? (:args t)))))

(defn- pure-term?
  "Pure host functions applied to locals, constants and pure terms."
  [t]
  (or (contains? #{:local :const} (:op t))
      (and (= :app (:op t))
           (= :host (get-in t [:fn :op]))
           (let [q (get-in t [:fn :name])]
             (or (and (= "clojure.core" (namespace q)) (contains? b/pure-host (symbol (name q))))
                 (:pure (b/lookup q))))
           (every? pure-term? (:args t)))))

(defn guard?
  "A guard cannot perform an effect, and fails only where the reference
   fails (L4.check.speculate): it is total, or it is the reference's own
   test (or its negation), which the reference evaluates first."
  [g reference]
  (or (total-guard? g)
      (and (pure-term? g)
           (= :if (:op reference))
           (let [own (term-key (:test reference))]
             (or (= (term-key g) own)
                 (and (= :app (:op g)) (= 'clojure.core/not (get-in g [:fn :name]))
                      (= own (term-key (first (:args g))))))))))

(defn- speculation? [t] (and (= :if (:op t)) (:speculate t)))

(defn- value-guard
  "[local-name constant-term] for a guard (same? x c), else nil."
  [t]
  (when (and (= :app (:op t)) (same-guard? (:fn t)))
    (let [[x c] (:args t)]
      (when (and (= :local (:op x)) (= :const (:op c))) [(:name x) c]))))

(defn equal?
  "Is `a` equivalent to `b` under the checker's rules?"
  [ctx a b]
  (let [a (whnf ctx a) b (whnf ctx b)]
    (or (identical? a b)                             ; the same term means the same
        (cond
          ;; L4.check.speculate: both branches must mean the other side
          (and (speculation? b) (not (speculation? a)))
          (and (guard? (:test b) (:else b))
               (if-let [[x c] (value-guard (:test b))]
                 ;; L4.check.speculate-value: under (same? x c) the branch means a with x := c
                 (equal? ctx (t/substitute a {x c}) (:then b))
                 ;; L4.check.speculate-assume: the branch means a where the guard holds
                 (equal? (assume ctx (:test b)) a (:then b)))
               (equal? ctx a (:else b)))
          (and (speculation? a) (not (speculation? b)))
          (and (guard? (:test a) (:else a)) (equal? ctx (:then a) b) (equal? ctx (:else a) b)))
        (and (= (:op a) (:op b)) (same-shape ctx a b))
        ;; a is on the reference's side, b on the candidate's (see check)
        (if-let [a' (unfold-head ctx a :reference)]
          (equal? ctx a' b)
          (when-let [b' (unfold-head ctx b :candidate)]
            (equal? ctx a b')))
        (do (when-not @(:difference ctx) (vreset! (:difference ctx) [a b]))
            false))))

(defn check
  "Compare `reference` and `candidate` terms in preparation world `world`,
   charging `meter` (a long array, or nil). `self` is the name of the
   definition being prepared, or nil (L4.check.self). Returns
     {:result :equal :premises #{[q g] ..}}
     {:result :different :difference [ref-form cand-form]}
     {:result :exhausted}"
  [reference candidate world meter & [self]]
  (let [ctx {:world world :meter meter :self self :premises (volatile! #{}) :difference (volatile! nil)}]
    (try
      (if (equal? ctx reference candidate)
        {:result :equal :premises @(:premises ctx)}
        {:result :different
         :difference (mapv t/->form @(:difference ctx))})
      (catch clojure.lang.ExceptionInfo e
        (if (::exhausted (ex-data e)) {:result :exhausted} (throw e))))))
