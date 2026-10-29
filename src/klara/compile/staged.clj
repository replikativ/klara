(ns klara.compile.staged
  "Closed code -> isolated prepared scalar candidate -> atomic cache install.
   The model generator and policy may run in Klara at any stage. This module
   is the trusted seed analyzer/backend, not a self-hosted compiler or proof."
  (:require [clojure.string :as str]
            [clojure.java.io :as io]
            [klara.authority :as authority]
            [klara.code :as code]
            [klara.core :as core]
            [klara.compile.ir :as ir]
            [klara.compile.scalar :as scalar]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as world])
  (:import [clojure.lang DynamicClassLoader]
           [java.nio.file Files]))

;; Prepared candidates are opaque capabilities to install only compiler-created
;; executables. They contain immutable code/requirements and a loaded function,
;; never an operational authority token, world reference or profile accumulator.
(deftype Prepared [source executable info])
(defmethod print-method Prepared [_ out] (.write ^java.io.Writer out "#<prepared-specialization>"))

(defn- fail [message] (throw (ex-info message {:reason :unsupported-region})))

(defn- entry-constants
  "Only mandatory leading scalar world reads may move to admission. A read
   under a branch or after arithmetic stays unsupported: eager recorder reads
   there would change exception/read order. Returns [body guards reads]."
  [body root]
  (if (and (= :let (:op body)) (= :resolve (get-in body [:init :op])))
    (let [sym (get-in body [:init :id]) entry (world/entry* root sym)]
      (when-not (and (= :def (:kind entry)) (not (world/pending? root entry))
                     (instance? Long (:value entry)))
        (fail "only current Long-valued entry reads are supported"))
      (let [[tail guards reads] (entry-constants (:body body) root)]
        [(assoc body :init {:op :quote :datum (:value entry)} :body tail)
         (conj guards [:world sym (:value-id entry)])
         (conj reads [:value sym (:value-id entry)])]))
    [body #{} #{}]))

(defn- java-source [name typed]
  (binding [scalar/*counter* (atom 0)]
    (let [params (mapv #(str "a" %) (range (count (:params typed))))]
      (str "package klara.generated;\npublic final class " name " extends clojure.lang.AFn {\n"
           "public static long body(" (str/join "," (map #(str "long " %) params)) ") {\n"
           (scalar/tail-code (:body typed) (zipmap (:params typed) params) {} false nil)
           "}\n@Override public Object invoke(" (str/join "," (map #(str "Object " %) params)) ") {\n"
           "return Long.valueOf(body(" (str/join "," (map #(str "((Long)" % ").longValue()") params)) "));\n}\n}\n"))))

(defn- emit! [source class-name]
  ;; Host compiler allocation is local to this job; neither a mutable compiler
  ;; context nor its directory is shared with operational Klara code.
  (let [dir (.toFile (Files/createTempDirectory "klara-staged-" (make-array java.nio.file.attribute.FileAttribute 0)))
        file (io/file dir (str class-name ".java"))]
    (try
      (spit file source)
      (let [compiler (javax.tools.ToolProvider/getSystemJavaCompiler)
            errors (java.io.ByteArrayOutputStream.)]
        (when-not compiler (fail "staged scalar backend requires a JDK compiler"))
        (when-not (zero? (.run compiler nil errors errors
                              (into-array String ["-proc:none" "-classpath" (System/getProperty "java.class.path")
                                                  "-d" (.getPath dir) (.getPath file)])))
          (throw (ex-info "staged scalar Java emission failed" {:diagnostic (str errors)}))))
      (let [bytes (Files/readAllBytes (.toPath (io/file dir "klara/generated" (str class-name ".class"))))
            loader (DynamicClassLoader. (.getContextClassLoader (Thread/currentThread)))
            klass (.defineClass loader (str "klara.generated." class-name) bytes nil)]
        {:function (.newInstance (.getDeclaredConstructor klass (make-array Class 0)) (object-array 0))
         :class-bytes (alength bytes) :java-source source})
      (finally (doseq [f (reverse (file-seq dir))] (io/delete-file f true))))))

(stage/register-checker!
 :klara.compile/staged-scalar
 (fn [exe]
   (when-not (and (= :tested (get-in exe [:certificate :kind]))
                  (= "staged-scalar-1" (get-in exe [:certificate :checker-version]))
                  (= (:code-id exe) (core/code-id (:generic exe)))
                  (= (:ir-digest exe) (core/sha256 (pr-str (:typed exe))))
                  (= (:ir-digest exe) (get-in exe [:certificate :ir-digest]))
                  (fn? (:run exe)))
     :invalid-scalar-executable)))

(defn prepare
  "Analyze/emit without publishing. Input must be closed code of a fixed
   function with <=4 Long arguments. The compiler gets an immutable root and
   a fresh authority store, never the caller's operational capabilities.
   Unsupported code declines before executing any source computation."
  [root source]
  (let [start (System/nanoTime)]
    (when-not (and (code/code? source) (code/closed? source)) (fail "prepare requires closed code"))
    (binding [authority/*store* (authority/new-store)
              ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
              ev/*outer-k* [] ev/*fiber* nil world/*reads* nil]
      (let [generic (code/s->core (code/code-term source)) named (ir/named generic)]
        (when-not (and (= :fn (:op named)) (not (:rest? named)) (<= 0 (:arity named) 4))
          (fail "prepare requires a fixed scalar function of at most four arguments"))
        (let [[body world-guards reads] (entry-constants (:body named) root)
              types (vec (repeat (:arity named) :long))
              body (scalar/analyze body (zipmap (:params named) types) {} nil)
              _ (scalar/require-type body :long)
              typed {:params (:params named) :body body :args types :return :long}
              cid (core/code-id generic)
              guards (into (into #{[:captures []] [:statics []] [:arity (:arity named)]
                                   [:unhandled #{:exn/raise}]} world-guards)
                           (map-indexed (fn [i _] [:arg i :long]) types))
              name (str "Scalar_" (subs cid 0 20))
              emitted (emit! (java-source name typed) name)
              f (:function emitted)
              run (fn [& args]
                    ;; Current invocation/current recorder; no persistent read flag.
                    (doseq [read reads] (world/note-read! read))
                    (ev/invoke-boxed f args))
              digest (core/sha256 (pr-str typed))
              cert (-> (stage/certify cid guards :klara.compile/staged-scalar
                                     {:suite "klara.staged-compile-test" :obligation :T0-equivalence})
                       (dissoc :digest)
                       (assoc :kind :tested :checker-version "staged-scalar-1" :ir-digest digest))
              exe {:code-id cid :generic generic :guards guards :typed typed :ir-digest digest
                   :run run :definition-reads reads :certificate (assoc cert :digest (stage/digest cert))}
              info (assoc (dissoc emitted :function) :code-id cid :guards guards
                          :compile-ms (/ (- (System/nanoTime) start) 1e6))]
          (Prepared. source exe info))))))

(defn prepared-info [^Prepared p] (dissoc (.-info p) ::validation))

(defn prevalidate
  "Discharge certificate checking in preparation, before publication. The
   opaque receipt binds the exact immutable executable and checker registry."
  [^Prepared p]
  (let [start (System/nanoTime) receipt (stage/validate-executable (.-executable p))]
    (Prepared. (.-source p) (.-executable p)
               (assoc (.-info p) ::validation receipt
                      :validation-ms (/ (- (System/nanoTime) start) 1e6)))))

(defn install!
  "Validate against the caller's pinned basis, then publish a complete
   executable with stage/install!'s single atomic cache update. A world
   adoption is separate. Existing pinned worlds keep their own verdicts."
  [cache root candidate]
  (when-not (instance? Prepared candidate) (fail "install requires a prepared candidate"))
  (when-not cache (fail "install requires an active stage cache"))
  (when (some #(contains? #{:branch :fork-run :fork-scope} (:tag %))
              (mapcat identity ev/*outer-k*))
    (throw (ex-info "install must follow fork exit; adoption and publication are separate"
                    {:klara/error :authority})))
  (let [exe (.-executable ^Prepared candidate)]
    (if (every? #(stage/guard-holds? % {:basis root}) (filter #(= :world (first %)) (:guards exe)))
      (do (if-let [receipt (::validation (.-info ^Prepared candidate))]
            (if (stage/validated-for? receipt exe)
              (stage/install-validated! cache receipt)
              (throw (ex-info "validation does not bind this executable" {:reason :validation-mismatch})))
            (stage/install! cache exe))
          {:status :installed :code-id (:code-id exe)})
      {:status :declined :reason :stale-world})))

(ev/register-reference-handler! :stage/layout
 (fn [[args] _]
   (if (and (vector? args) (every? #(instance? Long %) args)) :long :generic)))
(ev/register-reference-handler! :stage/prepare
 (fn [[source] env]
   (try (prepare (:basis env) source)
        (catch clojure.lang.ExceptionInfo e
          (if (= :unsupported-region (:reason (ex-data e)))
            {:status :declined :reason :unsupported-region}
            (throw e))))))
(ev/register-reference-handler! :stage/install
 (fn [[candidate] env]
   (if (instance? Prepared candidate) (install! stage/*cache* (:basis env) candidate) candidate)))
