(ns klara.region-aot
  "Trusted local AOT cache experiment. Stores JVM classfiles and data-only
   admission requirements. No new stage checker or production ABI."
  (:require [clojure.edn :as edn] [clojure.java.io :as io]
            [klara.compile.core :as cc] [klara.compile.requirements :as req]
            [klara.typed-regions :as regions] [klara.defs :as d]
            [klara.world :as w] [klara.eval :as ev])
  (:import [java.security MessageDigest] [java.util Base64]
           [java.nio.file Files] [clojure.lang DynamicClassLoader]))

(def format-version :klara.experimental/typed-aot-v1)
(defn sha [bytes]
  (.formatHex (java.util.HexFormat/of) (.digest (MessageDigest/getInstance "SHA-256") bytes)))
(defn target []
  {:java-feature (.feature (Runtime/version))
   :clojure (clojure-version) :numeric-contract :checked-long-v1})
(defn compiler-id []
  ;; Conservative source fingerprint: implementation edits invalidate local artifacts.
  (sha (.getBytes
        (pr-str (mapv (fn [f] [(.getPath f) (sha (Files/readAllBytes (.toPath f)))])
                      (sort-by #(.getPath %)
                               (concat (filter #(and (.isFile %) (.endsWith (.getName %) ".clj"))
                                               (file-seq (io/file "src/klara")))
                                       (map io/file ["experiments/typed_jit/regions.clj"
                                                     "experiments/typed_jit/aot.clj"])))))
        java.nio.charset.StandardCharsets/UTF_8)))

(defn build! [root artifact-path]
  ;; Build the same typed representation as S21; no profile is required.
  ;; The adapter still has the explicit f/g scalar restriction.
  (let [start (System/nanoTime)
        ge (cc/compile-def root 'g {:inline-fuel 0})
        fe (cc/compile-def root 'f {:inline-fuel 0})
        gt (regions/typed-function ge {})
        ft (regions/typed-function fe {'g gt})
        requirements (mapv :requirements [ft gt])
        id (:value-id (w/entry* root 'g))
        class-name (str "Aot_" (subs (sha (.getBytes (pr-str requirements) "UTF-8")) 0 20))
        dir (.toFile (Files/createTempDirectory "klara-aot-" (make-array java.nio.file.attribute.FileAttribute 0)))
        source (io/file dir (str class-name ".java"))]
    (try
      (spit source (regions/source class-name {'g gt 'f ft} 'f id))
      (let [javac (javax.tools.ToolProvider/getSystemJavaCompiler)]
        (when-not javac (throw (ex-info "AOT build requires a JDK compiler" {})))
        (when-not (zero? (.run javac nil System/out System/err
                              (into-array String ["-d" (.getPath dir) (.getPath source)
                                                  "experiments/typed_jit/Context.java"])))
          (throw (ex-info "AOT Java compilation failed" {}))))
      (let [classes (mapv (fn [name]
                            (let [bytes (Files/readAllBytes
                                         (.toPath (io/file dir "klara/typedprobe" (str name ".class"))))]
                              {:name (str "klara.typedprobe." name) :sha256 (sha bytes)
                               :bytes (.encodeToString (Base64/getEncoder) bytes)}))
                          ["Context" class-name])
            artifact {:format format-version :compiler-id (compiler-id) :target (target)
                      :requirements requirements :reads (:definition-reads fe)
                      :class (str "klara.typedprobe." class-name) :method "inline_f"
                      :classes classes}]
        (spit artifact-path (pr-str artifact))
        {:artifact artifact-path :build-ms (/ (- (System/nanoTime) start) 1e6)
         :class-bytes (reduce + (map #(alength (.decode (Base64/getDecoder) (:bytes %))) classes))})
      (finally
        (doseq [f (reverse (file-seq dir))] (io/delete-file f true))))))

(defn validate-artifact [a root]
  (cond
    (not= format-version (:format a)) :format-mismatch
    (not= (compiler-id) (:compiler-id a)) :compiler-mismatch
    (not= (target) (:target a)) :target-mismatch
    (not (and (vector? (:requirements a)) (= 2 (count (:requirements a)))
              (every? req/well-formed? (:requirements a)))) :bad-requirements
    (not (every? #(req/world-valid? % root) (:requirements a))) :world-mismatch
    (not= ['f 'g] (mapv #(get-in % [:source :name]) (:requirements a))) :entry-mismatch
    (not= [:long] (:inputs (first (:requirements a)))) :input-layout-mismatch
    (not= (:reads a) (set (for [[_ sym id] (mapcat :world (:requirements a))]
                           [:value sym id]))) :read-set-mismatch
    (not= "inline_f" (:method a)) :method-mismatch
    (not (and (vector? (:classes a)) (= 2 (count (:classes a)))
              (= #{"klara.typedprobe.Context" (:class a)} (set (map :name (:classes a))))
              (every? #(= (:sha256 %) (sha (.decode (Base64/getDecoder) (:bytes %))))
                      (:classes a)))) :class-integrity-mismatch
    :else nil))

(defn load! [artifact-path root]
  (let [start (System/nanoTime)]
    (try
      (let [a (edn/read-string (slurp artifact-path))]
        (if-let [reason (validate-artifact a root)]
          {:status :declined :reason reason}
          (let [loader (DynamicClassLoader. (.getContextClassLoader (Thread/currentThread)))
                classes (into {} (for [{:keys [name bytes]} (:classes a)]
                                   [name (.defineClass loader name (.decode (Base64/getDecoder) bytes) nil)]))
                method (.getMethod ^Class (get classes (:class a)) "inline_f" (into-array Class [Long/TYPE]))]
            {:status :loaded :requirements (:requirements a) :reads (:reads a)
             :method method :loader loader :stats (atom {:fast 0 :fallback 0})
             :load-ms (/ (- (System/nanoTime) start) 1e6)})))
      (catch Exception e {:status :declined :reason :invalid-artifact
                          :detail (.getMessage e)}))))

(defn invoke! [loaded root args]
  (when-not (= :loaded (:status loaded))
    (throw (ex-info "invoke requires an admitted artifact" loaded)))
  (let [requirements (:requirements loaded)
        valid? (and (every? #(req/world-valid? % root) requirements)
                    (req/call-valid? (first requirements) args ev/*outer-k*))]
    (if valid?
      (do
        (swap! (:stats loaded) update :fast inc)
        ;; Per invocation and recorder; never a persistent 'already read' flag.
        (doseq [read (:reads loaded)] (w/note-read! read))
        (try (.invoke ^java.lang.reflect.Method (:method loaded) nil (object-array args))
             (catch java.lang.reflect.InvocationTargetException e (throw (.getCause e)))))
      (do
        (swap! (:stats loaded) update :fallback inc)
        (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
          (ev/call-value (d/lookup root 'f) (vec args)))))))
