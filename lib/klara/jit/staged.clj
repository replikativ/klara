(ns klara.jit.staged
  "The staged interpreter (design/08-staged-jit.md, plan P7).

  One interpreter for Core, written against a domain. With `values` it
  computes: an interpreter, tested against the machine. With `staged` it
  computes what is known and generates code for the rest: the specializer.
  It reads terms only through views and builds code only with templates and
  the binder constructors (L2.code.binders), so every name it introduces is
  fresh and the extrusion check holds.

  A domain is a map of operations:
    :const v            a constant
    :host c :global c   what host or global code c denotes
    :if t then else     then and else are thunks: only the taken one runs
    :let init body      body is a function of the bound value
    :do xs              xs evaluated in order; the last is the value
    :fn n body          a function of n parameters; body takes self and them
    :app f args         a call
    :loop inits body    a loop; body takes its variables and a recur function"
  (:require [klara.code :as code]
            [klara.stage :refer [code esc lift run]]))

;; ---------------------------------------------------------------------------
;; Binding-time values (the staged domain)

(defn static
  "A known value; `c`, if given, is code that denotes it, kept in residuals
   instead of the lifted value (a host function, a data definition)."
  ([v] {::static true ::value v})
  ([v c] {::static true ::value v ::code c}))

(defn dynamic [c] {::static false ::code c})

(defn static? [x] (::static x))

(defn value [x] (::value x))

(defn ->code
  "Code for a binding-time value."
  [x]
  (if (static? x)
    (or (::code x) (lift (::value x)))
    (::code x)))

(defn- plain?
  "Plain data: what may become a static value by computation (no lazy
   sequences, functions or mutable objects)."
  [x]
  (cond (or (nil? x) (number? x) (boolean? x) (string? x) (keyword? x) (symbol? x) (char? x)) true
        (map? x) (every? (fn [[k v]] (and (plain? k) (plain? v))) x)
        (or (vector? x) (set? x)) (every? plain? x)
        :else false))

;; ---------------------------------------------------------------------------
;; The domains

(def values
  "Everything known: the generator computes."
  {:const (fn [v] v)
   :host (fn [c] (run c))
   :global (fn [c] (run c))
   :if (fn [t then else] (if t (then) (else)))
   :let (fn [init body] (body init))
   :do (fn [xs] (last xs))
   :fn (fn [n body] (letfn [(self [& args] (body self (vec args)))] self))
   :app (fn [f args] (apply f args))
   :loop (fn [inits body]
           (loop [args inits]
             (let [r (body args (fn [& as] {::recur (vec as)}))]
               (if (and (map? r) (contains? r ::recur)) (recur (::recur r)) r))))})

(defn- call-code [f args]
  (code/make {:op :app :fn (->code f) :args (mapv ->code args)}))

(defn- fold
  "A pure host function on static arguments, computed now: a static value,
   or nil when it fails or does not give plain data (the call then stays)."
  [f args]
  (when (and (static? f) (::code f) (code/pure-host? (::code f)) (every? static? args))
    (let [r (try [(apply (value f) (map value args))] (catch Exception e nil))]
      (when (and r (plain? (first r))) (static (first r))))))

(def staged
  "What is known is computed, the rest generated."
  {:const (fn [v] (static v))
   :host (fn [c] (static (run c) c))
   ;; a data definition is static; a function definition stays a call but
   ;; carries its code, so a call with known arguments can unfold it
   :global (fn [c] (if-let [k (code/known c)]
                     (static (:value (code/view k)) c)
                     (if-let [u (code/unfold c)]
                       (assoc (dynamic c) ::unfold u)
                       (dynamic c))))
   :if (fn [t then else]
         (if (static? t)
           (if (value t) (then) (else))
           (dynamic (code/make {:op :if :test (->code t) :then (->code (then)) :else (->code (else))}))))
   :let (fn [init body]
          (if (static? init)
            (body init)
            (dynamic (code (let [x (esc (->code init))]
                             (esc (->code (body (dynamic (code x))))))))))
   :do (fn [xs]
         (let [effects (filterv #(not (static? %)) (butlast xs))]   ; static values have no effects
           (if (empty? effects)
             (last xs)
             (dynamic (code/make {:op :do :body (conj (mapv ->code effects) (->code (last xs)))})))))
   :fn (fn [n body]
         (dynamic (code/fn* n (fn [self & ps] (->code (body (dynamic self) (mapv dynamic ps)))))))
   :app (fn [f args] (or (fold f args) (dynamic (call-code f args))))
   :loop (fn [inits body]
           (dynamic (code/loop* (mapv ->code inits)
                                (fn [ps recur-to]
                                  (->code (body (mapv dynamic ps)
                                                (fn [& as] (dynamic (apply recur-to (map ->code as))))))))))})

;; ---------------------------------------------------------------------------
;; The interpreter

(defn- recurs-to?
  "Does c contain a recur to `self`, not looking inside other functions?"
  [c self]
  (let [v (code/view c)]
    (or (and (= :recur (:op v)) (= self (:target v)))
        (and (not= :fn (:op v)) (boolean (some #(recurs-to? % self) (code/children c)))))))

(defn- loop-view
  "The function view of a loop application (a named one-arity function
   applied where it is made, recurring to itself), or nil."
  [v]
  (let [f (code/view (:fn v))]
    (when (and (= :fn (:op f)) (:self f) (:body f) (recurs-to? (:body f) (:self f)))
      f)))

(defn- trivial?
  "Dynamic code that may be used several times without repeating work: a
   local, a constant or a global."
  [x]
  (contains? #{:local :const :global} (:op (code/view (->code x)))))

(declare gen)

(defn- apply-known
  "Unfold known function f (its code in ::unfold) on args: its body generated
   with the parameters bound to the arguments in order; an argument that is
   dynamic and not trivial is bound by a let first, so it runs once."
  [dom f args env]
  (let [fv (code/view (::unfold f))]
    (letfn [(bind [ps as env]
              (if (empty? ps)
                (gen dom (:body fv) env)
                (let [a (first as)]
                  (if (or (static? a) (trivial? a))
                    (bind (rest ps) (rest as) (assoc env (first ps) a))
                    ((:let dom) a (fn [x] (bind (rest ps) (rest as) (assoc env (first ps) x))))))))]
      ;; the function's own name means the same known function
      (bind (:params fv) args (cond-> env (:self fv) (assoc (:self fv) f))))))

(defn- unfold?
  "Unfold a call of f on args: f is known with one fixed arity, some
   argument is known, and the generation's fuel is not spent."
  [env f args]
  (let [fuel (::fuel env)
        fv (when (::unfold f) (code/view (::unfold f)))]
    (when (and fuel fv (:body fv) (= (count (:params fv)) (count args))
               (some static? args) (pos? @fuel))
      (swap! fuel dec)
      true)))

(defn gen
  "Interpret Code c with domain dom in env (local name -> domain value)."
  [dom c env]
  (let [v (code/view c)]
    (case (:op v)
      :const ((:const dom) (:value v))
      :local (if (contains? env (:name v))
               (get env (:name v))
               (throw (ex-info (str "unbound local " (:name v)) {:name (:name v)})))
      :host ((:host dom) c)
      :global ((:global dom) c)
      :if ((:if dom) (gen dom (:test v) env)
                     (fn [] (gen dom (:then v) env))
                     (fn [] (gen dom (:else v) env)))
      :let ((:let dom) (gen dom (:init v) env)
                       (fn [i] (gen dom (:body v) (assoc env (:name v) i))))
      :do ((:do dom) (mapv (fn [b] (gen dom b env)) (:body v)))
      :fn (if (:body v)
            ((:fn dom) (count (:params v))
                       (fn [self ps]
                         (gen dom (:body v) (cond-> (merge env (zipmap (:params v) ps))
                                              (:self v) (assoc (:self v) self)))))
            (throw (ex-info "functions with several arities are not interpreted yet" {:op :fn})))
      :app (if-let [f (loop-view v)]
             ((:loop dom) (mapv (fn [a] (gen dom a env)) (:args v))
                          (fn [ps recur-to]
                            (gen dom (:body f) (assoc (merge env (zipmap (:params f) ps))
                                                      [::recur (:self f)] recur-to))))
             (let [f (gen dom (:fn v) env)
                   args (mapv (fn [a] (gen dom a env)) (:args v))]
               (if (unfold? env f args)
                 (apply-known dom f args env)
                 ((:app dom) f args))))
      :recur (apply (get env [::recur (:target v)]) (mapv (fn [a] (gen dom a env)) (:args v)))
      (throw (ex-info (str "not interpreted yet: " (:op v)) {:op (:op v)})))))

(defn interpret
  "Call function Code c on args, computing with the values domain."
  [c & args]
  (apply (gen values c {}) args))

(def fuel
  "Unfoldings of known functions one generation may do."
  64)

(defn residual
  "Code for function Code c generated with what it does not know dynamic:
   constants, data definitions and pure host functions on them are
   computed, known functions called with known arguments unfolded (up to
   `fuel` times). With nothing known it is the same function, rebuilt with
   fresh names."
  ([c] (residual c fuel))
  ([c n] (->code (gen staged c {::fuel (atom n)}))))
