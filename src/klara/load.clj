(ns klara.load
  "Bounded world-managed source loader. Trusted developer code, not a sandbox.
   ns and require support explicit :as dependencies; no host namespace loading."
  (:require [clojure.java.io :as io] [clojure.string :as str] [clojure.walk :as walk]
            [klara.core :as core] [klara.defs :as defs] [klara.eval :as ev]
            [klara.expand :as expand] [klara.world :as world]))

(defn- fail! [reason data] (throw (ex-info (str "loader: " (name reason)) (assoc data :klara/error :load))))
(defn descriptor [root module] (:value (world/entry* root (expand/module-id module))))

(defn- requirements [clauses]
  (mapv (fn [spec]
          (when-not (and (vector? spec) (symbol? (first spec))
                         (or (= 1 (count spec))
                             (and (= 3 (count spec)) (= :as (second spec)) (symbol? (nth spec 2)))))
            (fail! :require-subset {:spec spec}))
          [(first spec) (when (= 3 (count spec)) (nth spec 2))])
        (mapcat (fn [clause]
                  (when-not (and (seq? clause) (= :require (first clause)))
                    (fail! :ns-clause {:clause clause}))
                  (rest clause)) clauses)))

(defn- source [module {:keys [sources source-roots]}]
  (or (when-let [text (get sources module)] {:text text :path (str module)})
      (let [name (str module)]
        (when-not (re-matches #"[A-Za-z_][A-Za-z0-9_.-]*" name) (fail! :module-name {:module module}))
        (some (fn [root]
                (some (fn [ext]
                        (let [f (io/file root (str (-> name (str/replace "." "/") (str/replace "-" "_")) ext))]
                          (when (.isFile f) {:text (slurp f) :path (.getPath f)}))) [".cljc" ".clj"]))
              source-roots))
      (fail! :module-not-found {:module module})))

(declare load-into!)
(defn- require-into! [w module options stack]
  (when (some #{module} stack) (fail! :cyclic-require {:cycle (conj stack module)}))
  (when-not (:source-hash (descriptor (world/snapshot w) module))
    (let [{:keys [text path]} (source module options)]
      (load-into! w text (assoc options :expected module :path path) (conj stack module)))))

(defn declare! [w form options stack]
  (let [[_ module & clauses] form
        clauses (if (string? (first clauses)) (rest clauses) clauses)
        requires (requirements clauses)]
    (when-not (symbol? module) (fail! :ns-name {:form form}))
    (when (and (:expected options) (not= module (:expected options)))
      (fail! :wrong-module {:expected (:expected options) :actual module}))
    (doseq [[dependency] requires] (require-into! w dependency options stack))
    (let [value {:name module :aliases (into {} (keep (fn [[dep alias]] (when alias [alias dep]))) requires)
                 :requires (mapv first requires) :path (:path options) :source-hash (:source-hash options)}
          id (expand/module-id module)]
      (binding [expand/*module* nil] (defs/define! w (list 'def id (list 'quote value))))
      (defs/invalidate! w id))
    module))

(defn eval-form!
  "One trusted top-level guest form in a module. Definitions retain their
   module context for later dependency-driven re-expansion."
  [w module form]
  (binding [expand/*module* module ev/*fiber* (world/fiber w)]
    (let [root (world/snapshot w) expanded (expand/expand-recorded form root)]
      (if (contains? #{:def :macro} (:kind expanded))
        (let [result (defs/define-expanded! w form root expanded)]
          (defs/invalidate! w (:name result))
          {:definition (:name result)})
        {:value (ev/run (:term expanded) {:basis root :fiber ev/*fiber*})}))))

(defn read-form
  "An isolated reader namespace supplies aliases and syntax-quote naming.
   Its temporary prefix is normalized to the guest module and removed."
  [reader module aliases eof]
  (let [temporary (gensym "klara.reader") n (create-ns temporary)]
    (try
      (binding [*ns* n *read-eval* false]
        (refer 'clojure.core)
        (doseq [[a target] aliases] (alias a (create-ns target)))
        (let [form (read {:eof eof :read-cond :allow :features #{:klara}} reader)
              target (or module 'user)]
          (if (identical? form eof) eof
            (walk/postwalk
              (fn [x]
                (cond
                  (and (symbol? x) (= (str temporary) (namespace x)))
                  (with-meta (symbol (str target) (name x)) (meta x))
                  (and (keyword? x) (= (str temporary) (namespace x))) (keyword (str target) (name x))
                  :else x)) form))))
      (finally (remove-ns temporary)))))

(defn- load-into! [w text options stack]
  (with-open [r (clojure.lang.LineNumberingPushbackReader. (java.io.StringReader. text))]
    (let [eof (Object.) options (assoc options :source-hash (core/sha256 text))
          file (or (:path options) (Object.))]
      (loop [module (:namespace options) value nil forms 0]
        (let [form (read-form r module (:aliases (descriptor (world/snapshot w) module)) eof)]
          (if (identical? eof form)
            (do (when (and (:expected options) (not= module (:expected options)))
                  (fail! :missing-ns {:expected (:expected options)}))
                {:namespace module :value value :forms forms})
            (if (and (seq? form) (= 'ns (first form)))
              (recur (declare! w form options stack) nil (inc forms))
              (do
                (when (and (seq? form) (contains? '#{require use in-ns load load-file eval} (first form)))
                  (fail! :top-level-form {:form form}))
                (let [result (eval-form! w module form)]
                  (when-let [definitions (::preparation-definitions options)]
                    (when-let [name (:definition result)]
                      (swap! definitions conj {:name name :file file})))
                  (recur module result (inc forms)))))))))))

(defn load-string!
  "Stage definitions/dependencies in a temporary world and publish one root.
   Failure leaves definitions unchanged; external host effects are not undone.
   Concurrent publication declines instead of replaying initializers."
  ([w text] (load-string! w text {}))
  ([w text options]
   (let [base (world/snapshot w) child (world/make-world base)
         prepare? (= :baseline (:prepare options))
         definitions (when prepare? (atom []))
         result (load-into! child text (cond-> options prepare?
                                         (assoc ::preparation-definitions definitions)) [])
         published (world/snapshot child)]
     (when-not (compare-and-set! (:root w) base published)
       (fail! :publication-conflict {}))
     (if prepare?
       (assoc result :preparation
              (try ((requiring-resolve 'klara.compile.prepare/after-load!) published @definitions options)
                   (catch Exception e {:status :declined :reason :preparation-error})))
       result))))

(defn load-file!
  ([w path] (load-file! w path {}))
  ([w path options] (load-string! w (slurp path) (assoc options :path (str path)))))
