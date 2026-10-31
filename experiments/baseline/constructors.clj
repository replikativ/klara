(ns baseline.constructors
  "Paired literal/explicit map constructors after literal semantics were split."
  (:require [baseline.coverage :as coverage] [baseline.investment :as investment]
            [baseline.run :as base] [clojure.walk :as walk] [clojure.java.io :as io]
            [clojure.pprint :as pp] [klara.core :as core] [klara.expand :as expand]
            [klara.eval :as ev] [klara.world :as world] [klara.defs :as defs]))

(defn run-study! [process]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        literal (get-in coverage/workloads [:records :form])
        explicit (walk/postwalk #(if (and (map? %) (seq %)) (list* 'hash-map (mapcat identity %)) %) literal)
        _ (assert (not= (core/code-id (expand/expand-expr literal world/empty-root))
                     (core/code-id (expand/expand-expr explicit world/empty-root))))
        w (world/make-world) _ (defs/define! w (list 'def 'subject literal))
        explicit-world (world/make-world) _ (defs/define! explicit-world (list 'def 'subject explicit))
        explicit-root (world/snapshot explicit-world)
        explicit-f (:value (world/entry* explicit-root 'subject))
        root (world/snapshot w) f (:value (world/entry* root 'subject))
        variants {:clojure-literal {:value (:value (base/prepare :clojure literal))}
                  :clojure-explicit {:value (:value (base/prepare :clojure explicit))}
                  :baseline-literal (investment/compile-entry root f :baseline)
                  :baseline-explicit (investment/compile-entry explicit-root explicit-f :baseline)}
        expected ((get-in variants [:clojure-literal :value]) 5000)
        _ (dotimes [i 500]
            (doseq [e (investment/rotated (vec (sort (keys variants))) i) :let [p (get variants e)]]
              (investment/scope p #(assert (= expected ((:value p) 5000))))))
        samples (mapv (fn [i] (into {} (for [e (investment/rotated (vec (sort (keys variants))) i)]
                                               [e (investment/sample (get variants e) 5000 20)]))) (range 9))
        _ (assert (every? #(= expected (:value %)) (mapcat vals samples)))
        execution (into {} (for [[engine prepared] variants :when (:cache prepared)]
                             [engine (klara.stage/stats (:cache prepared))]))
        _ (doseq [[_ stats] execution]
            (assert (pos? (:hits stats)))
            (assert (zero? (:fallbacks stats)))
            (assert (zero? (:deopts stats))))
        report {:process (or process "0") :java (System/getProperty "java.runtime.version")
                :vm (System/getProperty "java.vm.name") :execution execution
                :warmup 500 :samples 9 :batch 20 :n 5000 :source literal :explicit-source explicit
                :core-id (core/code-id (expand/expand-expr literal world/empty-root))
                :source-sha256 (assoc (investment/source-hashes)
                                      "experiments/baseline/constructors.clj" (core/sha256 (slurp "experiments/baseline/constructors.clj"))
                                      "experiments/baseline/coverage.clj" (core/sha256 (slurp "experiments/baseline/coverage.clj")))
                :engines (into {} (for [e (keys variants) :let [s (mapv e samples)]]
                                   [e {:median-ns (base/median (map :ns-per-call s))
                                       :median-bytes (base/median (map :bytes-per-call s))
                                       :samples (mapv #(dissoc % :value) s)}]))}
        path (str "target/literal/constructors-" (or process "0") ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (prn (into {} (map (fn [[e v]] [e (select-keys v [:median-ns :median-bytes])])) (:engines report)))))

(defn -main [& [process]] (run-study! process) (shutdown-agents))
