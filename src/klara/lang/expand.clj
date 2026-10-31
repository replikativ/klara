(ns klara.lang.expand
  "Surface forms to Core terms (spec/L0-core.md#surface, spec/L2-staging.md).

  The expander knows nothing about worlds directly. It receives a resolver:
    {:ns        current namespace symbol
     :defined   (fn [q] definition-or-nil)      q is a qualified symbol
     :ns-info   (fn [ns] {:aliases {} :refers {} :exclude #{}} or nil)
     :run-macro (fn [macro-value form] expanded-form)}
  and returns a Core term. Errors are ex-info with :rule."
  (:require [clojure.string :as str]
            [klara.lang.builtins :as b]
            [klara.lang.term :as t]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; ---------------------------------------------------------------------------
;; Expansion environment
;;
;; :locals  {surface-symbol {:name unique :level n}}
;; :level   current stage (0 = present)
;; :codes   {level code-frame}: the code construction raising to that level;
;;          a code-frame is {:id :holes (atom [])}
;; :recur   {:target name :arity i :n count} for the enclosing loop/arity
;; :self    qualified name of the definition being expanded (for recursion)

(defn- host-ns
  "The host namespace mirroring a Klara namespace, used only for reading and
   for host macro expansion (syntax-quote resolves symbols against it)."
  [ns-sym]
  (let [n (create-ns ns-sym)]
    (when-not (get (ns-refers n) 'defn)
      (binding [*ns* n] (refer 'clojure.core)))
    n))

(defn mirror-alias!
  "Record a Klara alias in the host mirror (for syntax-quote)."
  [ns-sym alias target]
  (let [n (host-ns ns-sym)]
    (create-ns target)
    (when-not (get (ns-aliases n) alias)
      (.addAlias ^clojure.lang.Namespace n alias (the-ns target)))))

(defn mirror-refer!
  "Make syntax-quote qualify a referred Klara name to its home namespace."
  [ns-sym sym target-q]
  (let [n (host-ns ns-sym)
        v (intern (create-ns (symbol (namespace target-q))) (symbol (name target-q)))]
    (when-not (contains? (ns-interns n) sym)
      (when (get (ns-refers n) sym) (ns-unmap n sym))
      (try (.refer ^clojure.lang.Namespace n sym v) (catch Exception _ nil)))))

(defn read-all
  "Read every form of `s` in namespace `ns-sym` with the :klara feature (L0.surface.read).
   Returns a lazy-free vector. Reading is separate per form because `ns`
   changes the namespace: callers that need that use `read-one`."
  [reader ns-sym]
  (binding [*ns* (host-ns ns-sym) *read-eval* false]
    (read {:read-cond :allow :features #{:klara} :eof ::eof} reader)))

(defn eof? [x] (= x ::eof))

;; ---------------------------------------------------------------------------
;; Resolution

(defn- local-entry [env sym] (when-not (namespace sym) (get-in env [:locals sym])))

(defn- ns-info [env ns] (or ((:ns-info env) ns) {}))

(defn- klara-def [env q] ((:defined env) q))

(defn- host-var [sym]
  (let [v (ns-resolve (the-ns 'clojure.core) sym)]
    (when (var? v) v)))

(defn resolve-global
  "Resolve a non-local symbol. Returns one of
     {:kind :klara :name q :def d}   a world definition (maybe a macro)
     {:kind :builtin :name q :entry e}
     {:kind :host-var :var v :name q}
     {:kind :class :class c}
   or nil."
  [env sym]
  (let [cur (:ns env)
        info (ns-info env cur)
        builtin (fn [q] (when-let [e (b/lookup q)] {:kind :builtin :name q :entry e}))
        klara (fn [q] (when-let [d (klara-def env q)] {:kind :klara :name q :def d}))
        core (fn [s]
               (or (klara (symbol "klara.core" (name s)))
                   (builtin (symbol "klara.core" (name s)))
                   (when-let [v (host-var (symbol (name s)))]
                     {:kind :host-var :var v :name (symbol "clojure.core" (name s))})))]
    (if-let [nsp (namespace sym)]
      (let [target (or (get (:aliases info) (symbol nsp)) (symbol nsp))
            q (symbol (str target) (name sym))]
        (cond
          (= "clojure.core" (str target)) (core sym)
          :else (or (klara q) (builtin q)
                    (when (= (str target) (str cur)) (when (= q (:self env)) {:kind :klara :name q}))
                    (when-let [c (try (ns-resolve (host-ns cur) (symbol nsp)) (catch Exception _ nil))]
                      (when (class? c) {:kind :static :class c :member (name sym)})))))
      (let [q (symbol (str cur) (name sym))]
        (or (klara q)
            (when-let [r (get (:refers info) sym)] (or (klara r) (builtin r) {:kind :klara :name r}))
            (when (= q (:self env)) {:kind :klara :name q})
            (when-not (contains? (:exclude info) sym) (core sym))
            (when-let [c (try (ns-resolve (host-ns cur) sym) (catch Exception _ nil))]
              (when (class? c) {:kind :class :class c})))))))

(declare expand)

(defn- expand-body [env forms] (t/do* (mapv #(expand env %) (or (seq forms) [nil]))))

(defn- bind-local [env sym]
  (when (or (namespace sym) (not (symbol? sym)))
    (fail :L0.term.wf (str "cannot bind " (pr-str sym))))
  (let [n (t/fresh sym)]
    [n (assoc-in env [:locals sym] {:name n :level (:level env)})]))

;; ---------------------------------------------------------------------------
;; Special forms

(defn- expand-fn [env [_ & more]]
  (let [[self more] (if (symbol? (first more)) [(first more) (rest more)] [nil more])
        clauses (if (vector? (first more)) [more] more)
        [self-name env] (if self (bind-local env self) [(t/fresh "fn") env])
        arity (fn [i [params & body]]
                (when-not (vector? params) (fail :L0.term.wf "fn arity needs a parameter vector"))
                (let [[fixed [_ rest-sym]] (split-with #(not= '& %) params)
                      [names env] (reduce (fn [[ns env] p] (let [[n env] (bind-local env p)] [(conj ns n) env]))
                                          [[] env] fixed)
                      [rest-name env] (if rest-sym (bind-local env rest-sym) [nil env])
                      env (assoc env :recur {:target self-name :arity i
                                             :n (+ (count names) (if rest-name 1 0))})]
                  (t/arity names rest-name (expand-body env body))))]
    (t/fn-term self-name (vec (map-indexed arity clauses)))))

(defn- expand-let [env [_ bindings & body]]
  (when-not (and (vector? bindings) (even? (count bindings)))
    (fail :L0.term.wf "let needs a vector of pairs"))
  (letfn [(go [env [[s init] & more]]
            (if (nil? s)
              (expand-body env body)
              (let [init (expand env init)
                    [n env'] (bind-local env s)]
                (t/let1 n init (go env' more)))))]
    (go env (partition 2 bindings))))

(defn- expand-loop
  "(loop* [a x b y] body) => (let [a' x b' y] ((fn loop [a b] body) a' b'));
   recur in body re-enters the loop (L0.eval.tail)."
  [env [_ bindings & body]]
  (let [pairs (partition 2 bindings)
        syms (map first pairs)]
    (expand env (list 'let* (vec bindings)
                      (list* (list 'fn* (gensym "loop") (list (vec syms) (cons 'do body)))
                             syms)))))

(defn- expand-recur [env [_ & args]]
  (let [{:keys [target arity n]} (:recur env)]
    (when-not target (fail :L0.term.wf "recur outside loop or fn"))
    (when-not (= n (count args))
      (fail :L0.term.wf (str "recur expects " n " arguments, got " (count args))))
    {:op :recur :target target :arity arity :args (mapv #(expand env %) args)}))

(defn- expand-letfn [env [_ bindings & body]]
  (let [pairs (partition 2 bindings)
        [names env] (reduce (fn [[ns env] [s _]] (let [[n env] (bind-local env s)] [(conj ns n) env]))
                            [[] env] pairs)
        fns (mapv (fn [[_ f]] (expand env f)) pairs)]
    {:op :letrec :bindings (mapv vector names fns) :body (expand-body env body)}))

(defn- resolve-class [env sym]
  (let [c (try (ns-resolve (host-ns (:ns env)) sym) (catch Exception _ nil))]
    (if (class? c) c (fail :L1.resolve.unbound (str "unknown class " sym) :symbol sym))))

(defn- expand-try [env [_ & forms]]
  (let [catch? #(and (seq? %) (= 'catch (first %)))
        finally? #(and (seq? %) (= 'finally (first %)))
        body (remove #(or (catch? %) (finally? %)) forms)
        catches (filter catch? forms)
        fin (first (filter finally? forms))]
    {:op :try :body (expand-body env body)
     :catches (mapv (fn [[_ cls sym & cbody]]
                      (let [[n env'] (bind-local env sym)]
                        {:class (resolve-class env cls) :name n :body (expand-body env' cbody)}))
                    catches)
     :finally (when fin (expand-body env (rest fin)))}))

(defn- expand-dot [env [_ target & more]]
  (let [[member args] (if (seq? (first more)) [(ffirst more) (rest (first more))] [(first more) (rest more)])
        cls (when (symbol? target)
              (when-not (local-entry env target)
                (let [r (resolve-global env target)] (when (= :class (:kind r)) (:class r)))))]
    (if cls
      {:op :interop :static? true :target cls :member (str member) :args (mapv #(expand env %) args)}
      {:op :interop :static? false :target (expand env target) :member (str member)
       :args (mapv #(expand env %) args)})))

(defn- expand-new [env [_ cls & args]]
  {:op :interop :new? true :static? true :target (resolve-class env cls) :member "new"
   :args (mapv #(expand env %) args)})

(defn- expand-def [env [_ sym & more]]
  (let [[doc init] (if (and (string? (first more)) (next more)) [(first more) (second more)] [nil (first more)])
        q (symbol (str (:ns env)) (name sym))]
    (when (namespace sym) (fail :L0.term.wf "def of a qualified name"))
    (when (pos? (:level env)) (fail :L2.stage.level "def inside code"))
    {:op :def :name q :macro? (boolean (:macro (meta sym))) :doc doc
     :init (expand (assoc env :self q) init)}))

;; ---------------------------------------------------------------------------
;; Staging (spec/L2-staging.md)

(defn- expand-code [env [_ & body]]
  (let [level (inc (:level env))
        frame {:id (gensym "c") :holes (atom [])}
        inner (-> env (assoc :level level) (assoc-in [:codes level] frame))
        template (expand-body inner body)
        bound (into #{} (mapcat t/binders) (t/nodes template))
        free (remove bound (t/free-locals template))]
    {:op :code :id (:id frame) :template template :holes @(:holes frame) :free (vec (sort free))}))

(defn- expand-esc [env [_ g]]
  (let [level (:level env)]
    (when (zero? level) (fail :L2.esc.level "esc outside code"))
    (let [frame (get-in env [:codes level])
          hole (expand (assoc env :level (dec level)) g)
          i (count @(:holes frame))]
      (swap! (:holes frame) conj hole)
      {:op :hole :code (:id frame) :index i})))

;; ---------------------------------------------------------------------------
;; Directives and Klara-side macros

(defn- quoted [x] (if (and (seq? x) (= 'quote (first x))) (second x) x))

(defn- expand-case
  "Klara's case: a cond over = (L0.surface.unsupported names case*)."
  [env [_ e & clauses]]
  (let [v (gensym "case")
        default (when (odd? (count clauses)) (last clauses))
        pairs (partition 2 clauses)
        test (fn [k] (if (seq? k)
                       (list* 'clojure.core/or (map (fn [x] (list 'clojure.core/= v (list 'quote x))) k))
                       (list 'clojure.core/= v (list 'quote k))))]
    (expand env (list 'let* [v e]
                      (concat (list 'clojure.core/cond)
                              (mapcat (fn [[k r]] [(test k) r]) pairs)
                              [:else (if (odd? (count clauses)) default
                                       (list 'throw (list 'new 'IllegalArgumentException
                                                          (list 'clojure.core/str "No matching clause: " v))))])))))

(def ^:private specials
  {'quote (fn [_ [_ x]] (t/const x))
   'if (fn [env [_ c a b]] (t/if* (expand env c) (expand env a) (expand env b)))
   'do (fn [env [_ & body]] (expand-body env body))
   'let* expand-let
   'loop* expand-loop
   'recur expand-recur
   'fn* expand-fn
   'letfn* expand-letfn
   'def expand-def
   'throw (fn [env [_ e]] {:op :throw :ex (expand env e)})
   'try expand-try
   '. expand-dot
   'new expand-new})

(defn- directive [kind env form]
  (t/app (t/host (symbol "klara.kernel" (name kind))) [(t/const form) (t/const (:ns env))]))

(defn- expand-seq [env form]
  (let [op (first form)]
    (cond
      (and (symbol? op) (local-entry env op))
      (t/app (expand env op) (map #(expand env %) (rest form)))

      (and (symbol? op) (contains? specials op))
      ((specials op) env form)

      (and (symbol? op) (#{'ns 'in-ns 'require 'defmacro} op))
      (if (= op 'defmacro)
        (let [[_ name & more] form
              more (if (string? (first more)) (rest more) more)]
          (expand env (list 'def (vary-meta name assoc :macro true) (list* 'clojure.core/fn more))))
        (directive op env form))

      (and (symbol? op) (= 'case (symbol (name op))) (contains? #{nil "clojure.core" "klara.core"} (namespace op)))
      (expand-case env form)

      (symbol? op)
      (let [r (resolve-global env op)]
        (case (:kind r)
          :klara (if (get-in r [:def :macro?])
                   (expand env ((:run-macro env) (:def r) form))
                   (t/app (t/late (:name r)) (map #(expand env %) (rest form))))
          :builtin (let [e (:entry r)]
                     (case (:kind e)
                       :special (case (name (:name r))
                                  "code" (expand-code env form)
                                  "esc" (expand-esc env form))
                       :macro (expand env ((:fn e) form env))
                       (t/app (t/host (:name r)) (map #(expand env %) (rest form)))))
          :host-var (let [v (:var r) s (symbol (name (:name r)))]
                      (cond
                        (contains? b/unsupported s)
                        (fail :L0.surface.unsupported (str s " is not supported in Klara") :symbol s)
                        (:macro (meta v))
                        (expand env (binding [*ns* (host-ns (:ns env))]
                                      (apply @v form nil (rest form))))
                        :else (t/app (t/host (:name r)) (map #(expand env %) (rest form)))))
          :static (expand env (list* '. (symbol (.getName ^Class (:class r))) (symbol (:member r)) (rest form)))
          (let [s (str op)]
            (cond
              (str/starts-with? s ".") (expand env (list* '. (second form) (symbol (subs s 1)) (nnext form)))
              (str/ends-with? s ".") (expand env (list* 'new (symbol (subs s 0 (dec (count s)))) (rest form)))
              :else (fail :L1.resolve.unbound (str "unable to resolve " op " in " (:ns env)) :symbol op)))))

      :else (t/app (expand env op) (map #(expand env %) (rest form))))))

(defn- expand-symbol [env sym]
  (if-let [{:keys [name level]} (local-entry env sym)]
    (do (when (> level (:level env))
          (fail :L2.stage.level (str sym " is a later-stage variable used at an earlier stage") :symbol sym))
        (t/local name))
    (let [r (resolve-global env sym)]
      (case (:kind r)
        :klara (if (get-in r [:def :macro?])
                 (fail :L0.term.wf (str "cannot take the value of macro " sym))
                 (t/late (:name r)))
        :builtin (if (#{:special :macro} (get-in r [:entry :kind]))
                   (fail :L0.term.wf (str "cannot take the value of " sym))
                   (t/host (:name r)))
        :host-var (let [s (symbol (name (:name r)))]
                    (cond (contains? b/unsupported s) (fail :L0.surface.unsupported (str s " is not supported"))
                          (:macro (meta (:var r))) (fail :L0.term.wf (str "cannot take the value of macro " sym))
                          :else (t/host (:name r))))
        :class (t/const (:class r))
        :static {:op :interop :static? true :target (:class r) :member (:member r) :args []}
        (fail :L1.resolve.unbound (str "unable to resolve " sym " in " (:ns env)) :symbol sym)))))

(defn- literal-coll [env form]
  (let [items (if (map? form) (mapcat identity form) form)
        terms (mapv #(expand env %) items)]
    (if (every? #(= :const (:op %)) terms)
      (let [vals (map :value terms)]
        (t/const (cond (map? form) (apply hash-map vals)
                       (set? form) (set vals)
                       :else (vec vals))))
      (t/app (t/host (cond (map? form) 'clojure.core/hash-map
                           (set? form) 'clojure.core/hash-set
                           :else 'clojure.core/vector))
             terms))))

(defn expand
  "Expand one surface form to a Core term."
  [env form]
  (cond
    (symbol? form) (expand-symbol env form)
    (seq? form) (if (empty? form) (t/const ()) (expand-seq env form))
    (or (vector? form) (map? form) (set? form)) (literal-coll env form)
    :else (t/const form)))

(defn env
  "A top-level expansion environment over a resolver."
  [resolver]
  (merge {:locals {} :level 0 :codes {}} resolver))
