(ns klara.deploy-test
  (:require [clojure.test :refer [deftest is]] [clojure.java.io :as io] [clojure.edn :as edn]
            [klara.deploy :as deploy] [klara.world :as world] [klara.defs :as defs]
            [klara.eval :as ev] [klara.code :as code] [klara.stage :as stage])
  (:import [java.nio.file Files] [java.math BigInteger]))

(defn sample-world []
  (let [w (world/make-world)]
    (defs/define! w '(def bias 7))
    (defs/define! w '(def score (fn [x] (+ bias x)))) w))
(defn temp-directory [] (.toFile (Files/createTempDirectory "klara-deploy-test-" (make-array java.nio.file.attribute.FileAttribute 0))))
(defn cleanup! [directory] (doseq [file (reverse (file-seq directory))] (io/delete-file file true)))

(deftest portable-graph-preserves-numeric-representations-metadata-and-sharing
  (let [shared (with-meta [1 2] {:units :count})
        numbers [(int 1) (long 1) (bigint 1) (BigInteger. "1") 1.00M 1/3 (float 1) (double 1)]
        small-hash (assoc clojure.lang.PersistentHashMap/EMPTY :x 1)
        data {:a shared :b shared :numbers numbers :view (subvec [0 1 2] 1)
              :list '(a b) :map small-hash :set #{1 2} :symbol (with-meta 'x {:doc "x"})}
        decoded (deploy/decode-graph (deploy/encode-graph data))]
    (is (= data decoded))
    (is (identical? (:a decoded) (:b decoded)))
    (is (= {:units :count} (meta (:a decoded))))
    (is (= {:doc "x"} (meta (:symbol decoded))))
    (is (= (mapv class numbers) (mapv class (:numbers decoded))))
    (is (= (class small-hash) (class (:map decoded))))
    (is (= (class (:view data)) (class (:view decoded))))
    (is (= 2 (.scale ^java.math.BigDecimal (nth (:numbers decoded) 4)))))

(deftest unsupported-live-values-and-cycles-are-rejected
  (doseq [value [(atom 1) (long-array [1]) (fn [] 1) (world/make-world) (java.util.Date.)]]
    (is (thrown? clojure.lang.ExceptionInfo (deploy/encode-graph value))))
  (is (thrown? clojure.lang.ExceptionInfo
        (deploy/decode-graph {:root {:type :ref :id 0} :nodes [{:type :vector :items [{:type :ref :id 0}]}]})))
  (let [w (sample-world)]
    (defs/define! w '(def captured (let [x 3] (fn [] x))))
    (is (thrown? clojure.lang.ExceptionInfo (deploy/freeze (world/snapshot w) {}))))
  (let [root (world/put-entry world/empty-root 'raw {:kind :def :value 1 :reads #{} :value-id "raw"})]
    (is (thrown? clojure.lang.ExceptionInfo (deploy/freeze root {})))))

(deftest frozen-old-and-new-roots-restore-without-replaying-initializers
  (let [w (sample-world) old (world/snapshot w) old-bundle (deploy/freeze old {:steps 4})]
    (defs/define! w '(def bias 11))
    (let [new-bundle (deploy/freeze (world/snapshot w) {:steps 5})
          old-restored (deploy/restore old-bundle) new-restored (deploy/restore new-bundle)
          old-root (world/snapshot (:world old-restored)) new-root (world/snapshot (:world new-restored))]
      (is (= 10 (defs/eval-form old-root '(score 3))))
      (is (= 14 (defs/eval-form new-root '(score 3))))
      (is (= 10 (defs/eval-form old '(score 3))))
      (is (= (:value-id (world/entry* old 'bias)) (:value-id (world/entry* old-root 'bias))))
      (is (not= (:id old-bundle) (:id new-bundle)))
      (is (= {:steps 4} (:state old-restored)))
      (is (empty? (stage/executables (:cache old-restored))))
      (is (re-find #"def score" (deploy/source-projection old-bundle)))))
  (let [w (world/make-world) counter (atom 0)]
    (with-redefs [ev/reference-handlers (assoc ev/reference-handlers :stage/test-deploy-initializer (fn [_ _] (swap! counter inc)))]
      (defs/define! w '(def captured-data (perform :stage/test-deploy-initializer)))
      (let [restored (deploy/restore (deploy/freeze (world/snapshot w) {}))]
        (is (= 1 @counter))
        (is (= 1 (defs/lookup (world/snapshot (:world restored)) 'captured-data)))))))

(deftest integrity-host-compatibility-and-incoherent-roots-fail-closed
  (let [bundle (deploy/freeze (world/snapshot (sample-world)) {})
        payload (assoc-in (:payload bundle) [:host :java] "other-runtime")]
    (is (thrown? clojure.lang.ExceptionInfo (deploy/restore (assoc bundle :id "wrong"))))
    (is (thrown? clojure.lang.ExceptionInfo (deploy/restore {:id (deploy/content-id payload) :payload payload}))))
  (let [w (world/make-world)]
    (defs/define! w '(defmacro twice [x] (qq (+ ~x ~x))))
    (defs/define! w '(def score (fn [x] (twice x))))
    (defs/define! w '(defmacro twice [x] (qq (* ~x ~x))))
    (is (thrown? clojure.lang.ExceptionInfo (deploy/freeze (world/snapshot w) {}))))))

(deftest deployment-restores-in-a-fresh-JVM-with-empty-derived-caches
  (let [directory (temp-directory)]
    (try
      (let [bundle (deploy/freeze (world/snapshot (sample-world)) {:weights [(int 1) 1N (float 1)]})
            path (deploy/store! directory bundle)
            expression (str "(require '[klara.deploy :as b] '[klara.defs :as d] '[klara.world :as w] '[klara.stage :as s]) "
                            "(let [r (b/load! " (pr-str path) ") root (w/snapshot (:world r))] "
                            "(prn {:value (d/eval-form root '(score 3)) :id (:id r) "
                            ":classes (mapv (comp str class) (get-in r [:state :weights])) "
                            ":empty-cache (empty? (s/executables (:cache r)))}))")
            process (-> (ProcessBuilder. (into-array String ["java" "-Xmx512m" "-cp" (System/getProperty "java.class.path") "clojure.main" "-e" expression]))
                        (.redirectError (io/file directory "child.err")) (.start))
            output (slurp (.getInputStream process)) exit (.waitFor process)
            result (when (zero? exit) (edn/read-string output))]
        (is (zero? exit) (slurp (io/file directory "child.err")))
        (is (= 10 (:value result)))
        (is (= (:id bundle) (:id result)))
        (is (= ["class java.lang.Integer" "class clojure.lang.BigInt" "class java.lang.Float"] (:classes result)))
        (is (true? (:empty-cache result))))
      (finally (cleanup! directory)))))
