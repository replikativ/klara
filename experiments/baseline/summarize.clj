(ns baseline.summarize
  "Summarize independent JVM reports without mixing source cohorts."
  (:require [clojure.edn :as edn] [clojure.java.io :as io]
            [clojure.pprint :as pp] [clojure.string :as str]))

(defn summarize [paths]
  (let [reports (mapv #(edn/read-string (slurp %)) paths)
        cohort #(select-keys % [:source-sha256 :java :clojure :sci :os :jvm-arguments :measurement])]
    (assert (> (count reports) 1) "Need independent JVM reports")
    (assert (= (count reports) (count (set (map :process reports)))) "Duplicate process ID")
    (assert (apply = (map cohort reports)) "Source/runtime cohorts differ")
    (assert (apply = (map #(mapv (juxt :workload :n :expected) (:rows %)) reports))
            "Workloads or results differ")
    {:cohort (cohort (first reports)) :reports (vec paths)
     :aggregation :range-of-process-medians
     :rows (vec (for [index (range (count (:rows (first reports))))
                      engine [:clojure :sci :klara]
                      :let [row (get-in (first reports) [:rows index])
                            samples (mapv #(get-in % [:rows index :engines engine]) reports)]]
                  {:workload (:workload row) :n (:n row) :engine engine
                   :min-ns (apply min (map :median-ns samples))
                   :max-ns (apply max (map :median-ns samples))
                   :min-bytes (apply min (map :median-bytes samples))
                   :max-bytes (apply max (map :median-bytes samples))}))}))

(let [paths (if (seq *command-line-args*) *command-line-args*
             (mapv #(str "target/baseline/process-" % ".edn") (range 3)))
      result (summarize paths)
      output "target/baseline/summary.edn"]
  (io/make-parents output)
  (spit output (with-out-str (pp/pprint result)))
  (println (str/join "\t" ["workload" "n" "engine" "min-ns" "max-ns" "min-bytes" "max-bytes"]))
  (doseq [row (:rows result)]
    (println (str/join "\t" (map row [:workload :n :engine :min-ns :max-ns :min-bytes :max-bytes])))))
