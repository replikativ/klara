(ns klara.syntax
  "Syntax values and a small syntax-parse-style grammar. Inspired by Racket's
  syntax objects and syntax/parse (MIT/Apache-2.0); independently implemented."
  (:require [clojure.walk :as walk]
            [clojure.set :as set]))

(defrecord Syntax [datum scopes source properties])
(defn syntax? [x] (instance? Syntax x))
(def scope-key :klara.expand/scopes)

(defn- context-scopes [x]
  (or (scope-key (meta x))
      (let [identifiers (filter symbol? (tree-seq #(and (coll? %) (not (syntax? %))) seq x))]
        (when (seq identifiers)
          (apply set/intersection (map #(or (scope-key (meta %)) #{}) identifiers))))
      #{}))

(defn syntax
  "Wrap scoped reader data, retaining source position and properties."
  [x]
  (if (syntax? x) x
      (->Syntax x (context-scopes x)
                (select-keys (meta x) [:file :line :column :end-line :end-column]) {})))

(defn syntax-e [x] (:datum (syntax x)))
(defn syntax->datum [x]
  (walk/postwalk (fn [v] (if (syntax? v) (syntax->datum (:datum v))
                            (if (instance? clojure.lang.IObj v) (with-meta v nil) v)))
                 (syntax-e x)))
(defn datum->syntax
  "Give newly constructed datum the context's scopes and source. Existing
  embedded syntax values retain their own context."
  [context datum]
  (let [{:keys [scopes source properties]} (syntax context)
        d (letfn [(inherit [v]
                    (cond
                      (syntax? v) v
                      (symbol? v) (vary-meta v assoc scope-key scopes)
                      (list? v) (with-meta (apply list (map inherit v)) (meta v))
                      (vector? v) (with-meta (mapv inherit v) (meta v))
                      (map? v) (into (empty v) (map (fn [[k x]] [(inherit k) (inherit x)]) v))
                      (set? v) (into #{} (map inherit v))
                      :else v))]
            (inherit datum))]
    (->Syntax d scopes source properties)))

(defn reader-form
  "Expose syntax shells to the existing reader-form expander. Expanded
  syntax stays opaque: its named lexical references must survive splicing."
  [v]
  (cond
    (syntax? v) (if (get-in v [:properties :klara.expand/expanded]) v (reader-form (:datum v)))
    (seq? v) (with-meta
               (if (= 'quote-syntax (reader-form (first v)))
                 (cons 'quote-syntax (rest v))
                 (apply list (map reader-form v)))
               (meta v))
    (vector? v) (with-meta (mapv reader-form v) (meta v))
    (map? v) (into (empty v) (map (fn [[k x]] [(reader-form k) (reader-form x)]) v))
    (set? v) (into #{} (map reader-form v))
    :else v))
(defn syntax-property
  ([s k] (get (:properties (syntax s)) k))
  ([s k v] (assoc-in (syntax s) [:properties k] v)))

(defn canonicalize
  "Replace syntax literals in a value by scope-alpha-canonical trees.
  Identifier scopes inside datum participate even though ordinary datum
  metadata does not. Scope names are normalized jointly across the value."
  [value]
  (let [nodes (tree-seq coll? seq value)]
    (if-not (some syntax? nodes) value
      (let [ids (->> nodes
                 (mapcat #(if (syntax? %) (:scopes %) (scope-key (meta %))))
                 set sort (map-indexed (fn [i sc] [sc i])) (into {}))
            scope-set #(into #{} (map ids) %)]
        (letfn [(encode [v datum?]
                  (cond
                    (syntax? v) [::syntax (encode (:datum v) true)
                                 (scope-set (:scopes v))
                                 (encode (:source v) false) (encode (:properties v) false)]
                    (and datum? (symbol? v)) [::identifier (with-meta v nil)
                                              (scope-set (or (scope-key (meta v)) #{}))]
                    :else (walk/walk #(encode % datum?) identity v)))]
          (encode value false))))))

(defn fail!
  ([s expected path] (fail! s expected path nil))
  ([s expected path cause]
   (let [s (syntax s) loc (:source s)]
    (throw (ex-info (str "expand: expected " expected " at " (pr-str path)
                         (when (:line loc) (str " (" (or (:file loc) "source") ":"
                                                (:line loc) ":" (or (:column loc) 1) ")"))
                         (when cause (str ": " (ex-message cause))))
                    {:klara/error :expand :source loc :path path
                     :expected expected :datum (syntax->datum s)} cause)))))

(def ^:dynamic *classify*
  "Expansion-supplied expression checker and world syntax-class resolver." nil)
(def ^:dynamic *call-source* nil)
(def ^:dynamic *pattern-path* [])

(defn capture? [p]
  (and (vector? p) (symbol? (first p)) (keyword? (second p))))

(defn pattern-vars [p]
  (cond (capture? p) [(first p)]
        (sequential? p) (mapcat pattern-vars p)
        :else []))

(defn validate-pattern! [patterns]
  (let [vars (vec (pattern-vars patterns))]
    (when-not (vector? patterns) (fail! patterns "grammar vector" []))
    (when-not (= (count vars) (count (distinct vars)))
      (fail! patterns "distinct pattern variables" []))
    (letfn [(check [p]
              (cond
                (capture? p)
                (when-not (or (= 2 (count p)) (and (= 3 (count p)) (= '... (nth p 2))))
                  (fail! p "[name :class] or [name :class ...]" []))
                (and (seq? p) (contains? #{:optional :repeat} (first p)))
                (do (when-not (= 2 (count p)) (fail! p "one optional/repeated pattern" []))
                    (check (second p)))
                (sequential? p) (doseq [x p] (check x))))]
      (doseq [p patterns] (check p)))
    vars))

(defn syntax-attribute [s name]
  (get (syntax-property s ::attributes) name))

(declare match-one match-sequence)

(defn- located [s parent]
  (let [s (syntax s)]
    (if (seq (:source s)) s (assoc s :source (:source (syntax parent))))))

(defn- class-match [p s path]
  (let [[nm cls] p d (syntax-e s)
        value (case cls
                :binding (do (when-not (symbol? d) (fail! s "binding identifier" path)) s)
                :id (do (when-not (symbol? d) (fail! s "identifier" path)) s)
                :body s
                (if *classify* (*classify* cls s path)
                    (fail! s (str "active expansion for syntax class " cls) path)))]
    {nm (syntax value)}))

(defn match-one [p s path]
  (let [s (syntax s) d (syntax-e s)]
    (cond
      (capture? p) (class-match p s path)
      (sequential? p)
      (if (and (sequential? d) (= (vector? p) (vector? d)))
        (match-sequence p d path s)
        (fail! s (if (vector? p) "vector" "list") path))
      (= p d) {}
      :else (fail! s (pr-str p) path))))

(defn- attempt [f]
  (try {:value (f)}
       (catch clojure.lang.ExceptionInfo e
         (if (= :expand (:klara/error (ex-data e))) {:error e} (throw e)))))

(defn- best-error [a b]
  (if (pos? (compare (:path (ex-data a)) (:path (ex-data b)))) a b))

(defn match-sequence [patterns values path parent]
  (letfn [(run [ps vs i]
            (if-let [ps (seq ps)]
              (let [p (first ps)
                    repeated? (or (and (capture? p) (= '... (nth p 2 nil)))
                                  (and (seq? p) (= :repeat (first p))))
                    optional? (and (seq? p) (= :optional (first p)))
                    item (if (or optional? (and (seq? p) repeated?)) (second p) p)]
                (if (or repeated? optional?)
                  ;; Greedy, with backtracking so suffix literals and optional
                  ;; clauses do not consume each other's input.
                  (loop [ns (if repeated? (range (count vs) -1 -1) [1 0]) error nil]
                    (if-let [n (first ns)]
                      (let [result (attempt
                                     #(do
                                        (when (> n (count vs))
                                          (fail! parent (pr-str item) (conj path i)))
                                        (let [ms (mapv (fn [j v] (match-one item (located v parent) (conj path (+ i j))))
                                                       (range n) (take n vs))
                                              captured (into {} (for [v (pattern-vars item)]
                                                                   [v (if repeated? (mapv (fn [m] (get m v)) ms)
                                                                          (get (first ms) v))]))]
                                          (merge captured (run (next ps) (drop n vs) (+ i n))))))]
                        (if-let [e (:error result)]
                          (recur (next ns) (if error (best-error error e) e))
                          (:value result)))
                      (throw error)))
                  (if (seq vs)
                    (merge (match-one p (located (first vs) parent) (conj path i))
                           (run (next ps) (next vs) (inc i)))
                    (fail! parent (str "argument matching " (pr-str p)) (conj path i)))))
              (if (seq vs) (fail! (located (first vs) parent) "end of form" (conj path i)) {})))]
    (run patterns (seq values) 0)))

(defn syntax-match [patterns args]
  (let [parent (located args *call-source*)]
    (when-not (or (nil? args) (sequential? args))
      (fail! parent "syntax sequence" *pattern-path*))
    (match-sequence patterns args *pattern-path* parent)))
