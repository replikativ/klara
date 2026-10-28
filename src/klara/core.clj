(ns klara.core
  "Klara Core K0 (doc/01-core-v2.md §1): the twelve forms as data.

  A term is a map with an :op key. Locals are de Bruijn indices: index 0
  is the innermost binder. Binders push onto the environment in source
  order (fn parameters left to right, letrec bindings top to bottom), so
  the LAST parameter of a fn is index 0 in its body.

    {:op :local      :index n}
    {:op :quote      :datum d}                      datum quotation
    {:op :fn         :arity n :rest? b :body t}     binds n (+1 if rest?)
    {:op :app        :fn t :args [t ..]}
    {:op :let        :init t :body t}               binds 1
    {:op :if         :test t :then t :else t}
    {:op :letrec     :inits [fn ..] :body t}        binds (count inits) in
                                                    inits and body
    {:op :resolve    :id sym}                       read the pinned world
    {:op :prim       :name sym :args [t ..]}        portable algebra op
    {:op :perform    :target t|nil :name kw :args [t ..]}
    {:op :handle     :mode :lexical|:dynamic :clauses {kw t}
                     :return t|nil :body t}         body binds 1 (instance)
    {:op :specialize :fn t :args [t ..]}            s-m-n; reference
                                                    meaning = closure
    {:op :code       :body t}                       bracket: a code value
    {:op :esc        :body t}                       splice (inside :code)

  :code and :esc are the staging forms (doc/background/01-core-v2.md §6,
  S4): the body of :code is one level up, :esc moves one level down and
  is ill-formed at level 0. run, lift and genlet are ambient operations
  of the stage namespace, not forms. Binder nodes may carry
  :klara/names in METADATA (source binder names, used only to print
  generated code readably; never part of identity).

  perform with :target nil is an AMBIENT effect (namespaces world, host,
  exn, time, stage, auth) found by dynamic search; with a target it names a lexical
  handler instance (RFC 0002). handle in :lexical mode binds the instance
  it creates; in :dynamic mode it also binds it (uniform indexing) but is
  found by operation name.

  Identity (§3): CodeId = SHA-256 of the canonical serialization of a
  term. Locals are already indices, so α-equivalent terms are equal maps
  and the hash is α-canonical by construction; maps and sets inside
  quoted data are put in a deterministic order."
  (:import [java.security MessageDigest]))

(def forms
  #{:local :quote :fn :app :let :if :letrec :resolve :prim :perform :handle
    :specialize :code :esc})

(def ambient-namespaces #{"world" "host" "exn" "time" "stage" "auth"})

(defn ambient? [kw]
  (and (keyword? kw) (contains? ambient-namespaces (namespace kw))))

;; ---------------------------------------------------------------------------
;; Tier L primitives: names in the core, Clojure functions as their
;; reference implementation (same name, same behaviour on non-failing
;; programs — the naming rule).
;; ---------------------------------------------------------------------------

(def prims
  {'+ +, '- -, '* *, '/ /, 'quot quot, 'rem rem, 'mod mod, 'inc inc, 'dec dec
   '< <, '> >, '<= <=, '>= >=, '= =, 'not= not=, 'not not, 'zero? zero?
   'pos? pos?, 'neg? neg?, 'even? even?, 'odd? odd?, 'identity identity
   'list list, 'vector vector, 'hash-map hash-map, 'hash-set hash-set
   'cons cons, 'first first, 'second second, 'rest rest, 'next next
   'seq seq, 'empty? empty?, 'count count, 'nth nth, 'get get, 'assoc assoc
   'dissoc dissoc, 'conj conj, 'concat concat, 'vec vec, 'str str
   'keyword keyword, 'symbol symbol})

;; ---------------------------------------------------------------------------
;; constructors
;; ---------------------------------------------------------------------------

(defn local [i] {:op :local :index i})
(defn quote* [d] {:op :quote :datum d})
(defn lam ([arity body] (lam arity false body))
  ([arity rest? body] {:op :fn :arity arity :rest? (boolean rest?) :body body}))
(defn app [f & args] {:op :app :fn f :args (vec args)})
(defn app* [f args] {:op :app :fn f :args (vec args)})
(defn let1 [init body] {:op :let :init init :body body})
(defn if* [test then else] {:op :if :test test :then then :else else})
(defn letrec [inits body] {:op :letrec :inits (vec inits) :body body})
(defn resolve* [id] {:op :resolve :id id})
(defn prim [nm & args] {:op :prim :name nm :args (vec args)})
(defn perform [target nm & args]
  {:op :perform :target target :name nm :args (vec args)})
(defn handle
  ([mode clauses body] (handle mode clauses nil body))
  ([mode clauses return body]
   {:op :handle :mode mode :clauses clauses :return return :body body}))
(defn specialize [f & args] {:op :specialize :fn f :args (vec args)})
(defn code* [body] {:op :code :body body})
(defn esc [body] {:op :esc :body body})

;; ---------------------------------------------------------------------------
;; well-formedness: structure, scoping (indices in range), letrec inits
;; are fns, ambient/lexical discipline of perform and handle
;; ---------------------------------------------------------------------------

(def ^:private ^:dynamic *level* 0)

(defn- wf* [t depth path errs]
  (let [err (fn [errs msg] (conj errs {:path path :error msg :term t}))
        sub (fn [errs k t' d] (wf* t' d (conj path k) errs))
        subs (fn [errs k ts d]
               (if-not (vector? ts)
                 (err errs (str k " must be a vector"))
                 (reduce-kv (fn [e i t'] (wf* t' d (conj path k i) e)) errs ts)))]
    (if-not (and (map? t) (contains? forms (:op t)))
      (err errs "not a core term")
      (case (:op t)
        :local (let [i (:index t)]
                 (if (and (nat-int? i) (< i depth)) errs
                     (err errs (str "local index out of scope (depth " depth ")"))))
        :quote errs
        :fn (let [{:keys [arity rest? body]} t]
              (if-not (and (nat-int? arity) (boolean? rest?))
                (err errs "fn needs :arity nat and :rest? boolean")
                (sub errs :body body (+ depth arity (if rest? 1 0)))))
        :app (-> errs (sub :fn (:fn t) depth) (subs :args (:args t) depth))
        :let (-> errs (sub :init (:init t) depth) (sub :body (:body t) (inc depth)))
        :if (-> errs (sub :test (:test t) depth) (sub :then (:then t) depth)
                (sub :else (:else t) depth))
        :letrec (let [n (count (:inits t))
                      errs (if (every? #(= :fn (:op %)) (:inits t)) errs
                               (err errs "letrec inits must be fn terms"))]
                  (-> errs (subs :inits (:inits t) (+ depth n))
                      (sub :body (:body t) (+ depth n))))
        :resolve (if (symbol? (:id t)) errs (err errs "resolve needs a symbol"))
        :prim (let [errs (if (contains? prims (:name t)) errs
                             (err errs (str "unknown prim " (:name t))))]
                (subs errs :args (:args t) depth))
        :perform (let [{:keys [target name args]} t
                       errs (cond
                              (not (keyword? name)) (err errs "perform needs a keyword op")
                              (and (nil? target) (not (ambient? name)))
                              (err errs (str "untargeted perform of non-ambient op " name))
                              (and target (ambient? name))
                              (err errs (str "ambient op " name " cannot target an instance"))
                              :else errs)
                       errs (if target (sub errs :target target depth) errs)]
                   (subs errs :args args depth))
        :handle (let [{:keys [mode clauses return body]} t
                      errs (cond
                             (not (#{:lexical :dynamic} mode)) (err errs "bad handle mode")
                             (not (and (map? clauses) (every? keyword? (keys clauses))))
                             (err errs "clauses must map keywords to terms")
                             (and (= :dynamic mode) (not-every? ambient? (keys clauses)))
                             (err errs "dynamic handlers handle ambient ops only")
                             (and (= :lexical mode) (some ambient? (keys clauses)))
                             (err errs "lexical handlers handle user ops only")
                             :else errs)
                      errs (reduce-kv (fn [e k c] (wf* c depth (conj path :clauses k) e))
                                      errs (if (map? clauses) clauses {}))
                      errs (if return (sub errs :return return depth) errs)]
                  (sub errs :body body (inc depth)))
        :specialize (-> errs (sub :fn (:fn t) depth) (subs :args (:args t) depth))
        :code (binding [*level* (inc *level*)] (sub errs :body (:body t) depth))
        :esc (if (pos? *level*)
               (binding [*level* (dec *level*)] (sub errs :body (:body t) depth))
               (err errs "esc outside code"))))))

(defn wf-errors
  "Well-formedness errors of term t under depth enclosing binders."
  ([t] (wf-errors t 0))
  ([t depth] (wf* t depth [] [])))

(defn wf? [t] (empty? (wf-errors t)))

(defn assert-wf! [t]
  (when-let [es (seq (wf-errors t))]
    (throw (ex-info "klara.core: ill-formed term" {:errors (vec es)})))
  t)

;; ---------------------------------------------------------------------------
;; canonical form + CodeId
;; ---------------------------------------------------------------------------

(defn- canon [x]
  (cond
    (record? x) [:record (.getName (class x)) (canon (into {} x))]
    (map? x)    (into [:map] (sort-by pr-str (map (fn [[k v]] [(canon k) (canon v)]) x)))
    (set? x)    (into [:set] (sort-by pr-str (map canon x)))
    (vector? x) (into [:vec] (map canon x))
    (seq? x)    (into [:seq] (map canon x))
    :else x))

(defn canonical
  "Versioned canonical serialization tree. Datum metadata (scopes) never
  participates: it is not printed."
  [t]
  [:klara/core 0 (canon t)])

(defn sha256 [s]
  (let [d (MessageDigest/getInstance "SHA-256")
        bs (.digest d (.getBytes ^String s "UTF-8"))]
    (apply str (map #(format "%02x" %) bs))))

(def code-id
  "CodeId of a term: hash of its α-canonical form, frozen before
  optimization. Memoized (terms are immutable values)."
  (memoize
   (fn [t]
     (sha256 (binding [*print-meta* false *print-length* nil *print-level* nil]
               (pr-str (canonical t)))))))

;; ---------------------------------------------------------------------------
;; traversal helpers
;; ---------------------------------------------------------------------------

(defn children [t]
  (case (:op t)
    (:local :quote :resolve) []
    :fn [(:body t)]
    :app (into [(:fn t)] (:args t))
    :let [(:init t) (:body t)]
    :if [(:test t) (:then t) (:else t)]
    :letrec (conj (:inits t) (:body t))
    :prim (:args t)
    :perform (cond->> (:args t) (:target t) (into [(:target t)]))
    :handle (cond-> (into (vec (vals (:clauses t))) [(:body t)])
              (:return t) (conj (:return t)))
    :specialize (into [(:fn t)] (:args t))
    (:code :esc) [(:body t)]))

(defn free-globals
  "Symbols a term resolves in the world."
  [t]
  (into #{} (comp (filter #(= :resolve (:op %))) (map :id))
        (tree-seq (comp seq children) children t)))
