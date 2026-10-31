(ns interpreter.activation-followup
  "Separate cohort: warmed small calls and recovery at matched logical states."
  (:require [interpreter.activation :as a] [interpreter.bridge :as b]
            [interpreter.activation-bench :as bench]
            [interpreter.mutable-bench :as cases]
            [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.core :as core] [klara.expand :as x] [klara.world :as w]))

(defn paired [operations process repetitions]
  (let [pairs (mapv (fn [i]
                      (into {} (for [engine (if (even? (+ process i)) [:nodes :activation] [:activation :nodes])]
                                 [engine (bench/sample (operations engine) repetitions)]))) (range 9))]
    (into {} (for [engine [:nodes :activation]]
               [engine (bench/summarize (mapv engine pairs))]))))

(defn small-calls [process]
  (let [term (x/expand-expr (:form (nth cases/workloads 4)) w/empty-root)
        artifacts {:nodes (b/prepare term) :activation (a/prepare term)}
        operations (into {} (for [[engine artifact] artifacts] [engine #(b/invoke artifact 10000)]))
        sink (volatile! nil)
        _ (dotimes [i 10000]
            (doseq [engine (if (even? (+ i process)) [:nodes :activation] [:activation :nodes])]
              (vreset! sink ((operations engine)))))
        result (paired operations process 1000)]
    (assert (= 20003 @sink))
    (assert (every? #(= 20003 (:value %)) (mapcat :samples (vals result))))
    result))

(defn recovery [process]
  (let [term (x/expand-expr (:form (last cases/workloads)) w/empty-root)
        {:keys [nodes activation logical-frames]} (bench/matching-snapshots term)
        snapshots {:nodes (b/freeze nodes) :activation (b/freeze activation)}
        operations (into {} (for [[engine snapshot] snapshots]
                              [engine #(b/transfer! (b/thaw snapshot))]))
        sink (volatile! nil)
        _ (dotimes [_ 100]
            (doseq [engine [:nodes :activation]] (vreset! sink ((operations engine)))))
        pairs (paired operations process 100)]
    ;; Do not retain measured state graphs as report data.
    (doseq [data (vals pairs)]
      (assert (= 987 (b/resume! (:value (last (:samples data)))))))
    {:logical-frames logical-frames :operation [:thaw :transfer]
     :engines (into {} (for [[engine data] pairs]
                        [engine (update data :samples #(mapv (fn [sample] (dissoc sample :value)) %))]))}))

(defn -main [& [process]]
  (let [process (Long/parseLong (or process "0"))
        small (small-calls process) recovery (recovery process)
        files (concat ["deps.edn"]
                      (map str (filter #(.isFile %) (file-seq (io/file "src"))))
                      (map str (filter #(and (.isFile %) (.endsWith (.getName %) ".clj"))
                                       (file-seq (io/file "experiments/interpreter")))))
        report {:process process :java (System/getProperty "java.runtime.version") :clojure (clojure-version)
                :jvm-arguments (vec (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean)))
                :measurement {:small-warmup-per-engine 10000 :samples 9 :small-calls-per-sample 1000
                              :recovery-warmup 100 :recovery-calls-per-sample 100 :order :alternating}
                :source-sha256 (into {} (for [p files] [p (core/sha256 (slurp p))]))
                :limits [:closed-pure-fragment :one-small-function :one-snapshot-shape
                         :one-machine :retained-heap-not-measured :source-expansion-excluded]
                :small-calls small :recovery recovery}
        output (str "target/interpreter/activation-followup-" process ".edn")]
    (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
    (println :small (into {} (for [[engine d] small] [engine (select-keys d [:median-ns :median-bytes])])) )
    (println :recovery (into {} (for [[engine d] (:engines recovery)] [engine (select-keys d [:median-ns :median-bytes])])) )
    (println :report output))
  (shutdown-agents))
