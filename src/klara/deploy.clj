(ns klara.deploy
  "Versioned, content-addressed deployment bundles for a restricted portable
   world. Restores source/Core/data and open top-level functions, never live
   authority, continuations, native functions or opaque host objects. The graph
   codec preserves supported numeric classes, metadata and shared containers.
   This is a deployment boundary, not an arbitrary process checkpoint."
  (:require [clojure.edn :as edn] [clojure.java.io :as io] [clojure.string :as str]
            [klara.core :as core] [klara.code :as code] [klara.eval :as ev]
            [klara.world :as world] [klara.stage :as stage])
  (:import [java.util IdentityHashMap UUID]
           [java.math BigInteger BigDecimal]
           [java.nio.file Files StandardCopyOption]
           [java.io FileOutputStream]))

(def format-id :klara/deployment-1)
(def max-file-bytes (* 16 1024 1024))
(defn- reject! [check] (throw (ex-info "unsupported deployment bundle" {:reason :deployment :check check})))
(defn- printed [value]
  (binding [*print-meta* false *print-length* nil *print-level* nil *print-readably* true *print-dup* false]
    (pr-str value)))
(defn- canonical-wire [value]
  (cond
    (map? value) (into (sorted-map-by #(compare (printed %1) (printed %2)))
                       (map (fn [[key val]] [key (canonical-wire val)])) value)
    (vector? value) (mapv canonical-wire value)
    :else value))
(defn content-id [value] (core/sha256 (printed (canonical-wire value))))

(defn host-profile
  "Declared checkout/runtime compatibility fingerprint. This is not a proof
   that loaded host code implements the source. Use a fresh bootstrap when
   changing trusted host code; no hot host-upgrade protocol is provided."
  []
  {:clojure (clojure-version) :java (System/getProperty "java.runtime.version")
   :source (into (sorted-map)
                 (for [file (file-seq (io/file "src/klara"))
                       :when (and (.isFile file) (str/ends-with? (.getName file) ".clj"))]
                   [(.getPath file) (core/sha256 (slurp file))]))
   :dependencies (core/sha256 (slurp "deps.edn"))})

(defn encode-graph [value]
  (let [seen (IdentityHashMap.) nodes (atom [])]
    (letfn [(encode [value depth]
              (when (> depth 256) (reject! :graph-depth))
              (let [type (class value)
                    metadata (when-let [m (meta value)] (encode m (inc depth)))
                    scalar (cond
                             (nil? value) {:type :nil}
                             (boolean? value) {:type :boolean :value value}
                             (= Long type) {:type :long :value (str value)}
                             (= Integer type) {:type :int :value (str value)}
                             (= clojure.lang.BigInt type) {:type :bigint :value (str value)}
                             (= BigInteger type) {:type :biginteger :value (str value)}
                             (= BigDecimal type) {:type :decimal :value (.toString ^BigDecimal value)}
                             (= Double type) {:type :double :bits (Double/doubleToRawLongBits value)}
                             (= Float type) {:type :float :bits (long (Float/floatToRawIntBits value))}
                             (= clojure.lang.Ratio type) {:type :ratio :numerator (str (.numerator ^clojure.lang.Ratio value))
                                                         :denominator (str (.denominator ^clojure.lang.Ratio value))}
                             (string? value) (do (when (> (count value) 1048576) (reject! :string-size)) {:type :string :value value})
                             (char? value) {:type :char :value (str value)}
                             (keyword? value) {:type :keyword :namespace (namespace value) :name (name value)}
                             (symbol? value) {:type :symbol :namespace (namespace value) :name (name value)}
                             (= UUID type) {:type :uuid :value (str value)})]
                (if scalar (cond-> scalar metadata (assoc :metadata metadata))
                  (if (.containsKey seen value) {:type :ref :id (.get seen value)}
                    (let [id (count @nodes)
                          _ (when (>= id 65536) (reject! :graph-size))
                          _ (.put seen value id) _ (swap! nodes conj nil)
                          child #(encode % (inc depth))
                          node
                          (cond
                            (code/code? value)
                            (do (when-not (code/closed? value) (reject! :open-code))
                                {:type :code :core (child (code/s->core (code/code-term value)))})
                            (= clojure.lang.PersistentVector type) {:type :vector :items (mapv child value)}
                            (= clojure.lang.APersistentVector$SubVector type) {:type :subvector :items (mapv child value)}
                            (#{clojure.lang.PersistentList clojure.lang.PersistentList$EmptyList} type)
                            {:type :list :items (mapv child value)}
                            (= clojure.lang.PersistentArrayMap type)
                            {:type :array-map :entries (mapv (fn [[k v]] [(child k) (child v)]) value)}
                            (= clojure.lang.PersistentHashMap type)
                            {:type :hash-map :entries (mapv (fn [[k v]] [(child k) (child v)]) value)}
                            (= clojure.lang.PersistentHashSet type) {:type :set :items (mapv child value)}
                            :else (reject! :opaque-or-mutable-value))]
                      (swap! nodes assoc id (cond-> node metadata (assoc :metadata metadata)))
                      {:type :ref :id id})))))]
      (let [root (encode value 0)] {:root root :nodes @nodes}))))

(defn decode-graph [{:keys [root nodes]}]
  (when-not (and (vector? nodes) (<= (count nodes) 65536)) (reject! :graph-size))
  (let [cache (atom {}) active (atom #{})]
    (letfn [(decode [value depth]
              (when (> depth 256) (reject! :graph-depth))
              (let [child #(decode % (inc depth))
                    result
                    (case (:type value)
                      :nil nil :boolean (boolean (:value value))
                      :long (Long/parseLong (:value value)) :int (Integer/parseInt (:value value))
                      :bigint (bigint (BigInteger. ^String (:value value)))
                      :biginteger (BigInteger. ^String (:value value))
                      :decimal (BigDecimal. ^String (:value value))
                      :double (Double/longBitsToDouble (:bits value))
                      :float (Float/intBitsToFloat (int (:bits value)))
                      :ratio (clojure.lang.Ratio. (BigInteger. ^String (:numerator value)) (BigInteger. ^String (:denominator value)))
                      :string (:value value) :char (first (:value value))
                      :keyword (keyword (:namespace value) (:name value)) :symbol (symbol (:namespace value) (:name value))
                      :uuid (UUID/fromString (:value value))
                      :ref (let [id (:id value)]
                             (when-not (and (integer? id) (<= 0 id) (< id (count nodes))) (reject! :reference))
                             (if (contains? @cache id) (get @cache id)
                               (do (when (contains? @active id) (reject! :cycle))
                                   (swap! active conj id)
                                   (let [decoded (child (nth nodes id))]
                                     (swap! active disj id) (swap! cache assoc id decoded) decoded))))
                      :code (let [core (child (:core value))]
                              (core/assert-wf! core) (code/->code (code/core->s core)))
                      :vector (mapv child (:items value))
                      :subvector (subvec (mapv child (:items value)) 0)
                      :list (apply list (map child (:items value)))
                      :array-map (apply array-map (mapcat (fn [[k v]] [(child k) (child v)]) (:entries value)))
                      :hash-map (reduce (fn [m [k v]] (assoc m (child k) (child v))) clojure.lang.PersistentHashMap/EMPTY (:entries value))
                      :set (into #{} (map child (:items value)))
                      (reject! :wire-type))]
                (if-let [metadata (:metadata value)] (with-meta result (child metadata)) result)))]
      (decode root 0))))

(defn freeze
  "Capture an admitted source-backed root and explicit immutable application
   state. No initializer is replayed. Captured/pinned closures and live rights
   decline; executable caches are deliberately omitted."
  [root state]
  (let [entries
        (mapv
          (fn [[symbol entry]]
            (when-not (and (#{:def :macro} (:kind entry)) (:form entry) (:code entry)
                           (not (world/pending? root entry))
                           (= (:code-id entry) (core/code-id (:code entry)))) (reject! :definition))
            (core/assert-wf! (:code entry))
            (let [function? (ev/closure? (:value entry))]
              (when (and function?
                         (not (and (= :fn (get-in entry [:code :op]))
                                   (nil? (ev/closure-basis (:value entry)))
                                   (empty? (ev/closure-locals (:value entry)))
                                   (= (:code-id entry) (core/code-id (ev/closure-term (:value entry)))))))
                (reject! :captured-or-pinned-function))
              (when (and (= :macro (:kind entry)) (not function?)) (reject! :macro-value))
              {:symbol symbol :mode (if function? :open-function :data)
               :entry (dissoc entry :value)
               :value (when-not function? (:value entry))}))
          (sort-by (comp str key) (:defs root)))
        payload {:format format-id :host (host-profile)
                 :observation-profile :supported-immutable-values-and-open-functions
                 :graph (encode-graph {:version (:version root) :entries entries :state state})}]
    {:id (content-id payload) :payload payload}))

(defn restore
  "Validate compatibility/content and restore a fresh world with an empty cache.
   Source is retained for inspection; stored Core and data are authoritative.
   Does not resume a continuation or run an application entry point."
  [{:keys [id payload]}]
  (when-not (and (= format-id (:format payload)) (= id (content-id payload))) (reject! :content))
  (when-not (= (host-profile) (:host payload)) (reject! :host-profile))
  (let [{:keys [version entries state]} (decode-graph (:graph payload))
        root
        (do (when-not (and (integer? version) (<= 0 version) (vector? entries)
                           (= (count entries) (count (set (map :symbol entries))))
                           (every? #(symbol? (:symbol %)) entries)) (reject! :root-shape))
        (reduce
          (fn [root {:keys [symbol mode entry value]}]
            (when-not (and (:form entry) (:code entry) (#{:def :macro} (:kind entry))
                           (= (:code-id entry) (core/code-id (:code entry)))) (reject! :definition))
            (core/assert-wf! (:code entry))
            (let [value (case mode
                          :open-function (do (when-not (= :fn (get-in entry [:code :op])) (reject! :function))
                                             (ev/run (:code entry) {:basis world/empty-root :mint nil}))
                          :data value
                          (reject! :definition-mode))]
              (when (and (= :macro (:kind entry)) (not (ev/closure? value))) (reject! :macro-value))
              (world/put-entry root symbol (assoc entry :value value))))
          world/empty-root entries))
        ;; Rebuild reverse dependencies, preserving the captured root and entry
        ;; version metadata rather than inventing new history during loading.
        root (assoc root :version version :defs
                    (into {} (map (fn [{:keys [symbol entry]}]
                                    [symbol (assoc (world/entry* root symbol) :version (:version entry) :history (:history entry))])) entries))]
    (when (some #(world/pending? root %) (vals (:defs root))) (reject! :pending-dependency))
    {:world (world/make-world root) :state state :cache (stage/make-cache) :id id}))

(defn store! [directory bundle]
  (when-not (= (:id bundle) (content-id (:payload bundle))) (reject! :content))
  (let [directory (io/file directory) _ (.mkdirs directory)
        text (printed (canonical-wire bundle)) bytes (.getBytes text "UTF-8")
        _ (when (> (alength bytes) max-file-bytes) (reject! :bundle-size))
        target (io/file directory (str (:id bundle) ".edn"))
        temp (.toFile (Files/createTempFile (.toPath directory) "klara-deploy-" ".tmp"
                                            (make-array java.nio.file.attribute.FileAttribute 0)))]
    (try
      (with-open [out (FileOutputStream. temp)] (.write out bytes) (.sync (.getFD out)))
      (Files/move (.toPath temp) (.toPath target)
                  (into-array StandardCopyOption [StandardCopyOption/ATOMIC_MOVE StandardCopyOption/REPLACE_EXISTING]))
      (.getPath target)
      (finally (io/delete-file temp true)))))

(defn load! [path]
  (let [file (io/file path)]
    (when (> (.length file) max-file-bytes) (reject! :bundle-size))
    (with-open [reader (java.io.PushbackReader. (io/reader file))]
      (let [bundle (edn/read {:readers {} :default (fn [_ _] (reject! :reader-tag))} reader)]
        (when-not (= ::end (edn/read {:eof ::end} reader)) (reject! :trailing-data))
        (when (re-matches #"[0-9a-f]{64}\.edn" (.getName file))
          (when-not (= (.getName file) (str (:id bundle) ".edn")) (reject! :path-content-id)))
        (restore bundle)))))

(defn source-projection [bundle]
  (when-not (= (:id bundle) (content-id (:payload bundle))) (reject! :content))
  (let [{:keys [entries]} (decode-graph (get-in bundle [:payload :graph]))]
    (str ";; Source inspection projection of deployment " (:id bundle) "\n"
         ";; Restore the Core/value manifest for the exact captured state.\n"
         (str/join "\n\n" (map #(binding [*print-meta* true] (pr-str (get-in % [:entry :form]))) entries)) "\n")))
