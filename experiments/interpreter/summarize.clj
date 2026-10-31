(ns interpreter.summarize
  (:require [clojure.edn :as edn] [clojure.java.io :as io]
            [clojure.pprint :as pp] [clojure.string :as str]))

(let [paths (mapv #(str "target/interpreter/process-" % ".edn") (range 3))
      reports (mapv #(edn/read-string (slurp %)) paths)
      cohort #(select-keys % [:source-sha256 :java :clojure :os :jvm-arguments :measurement])
      span (fn [xs] [(apply min xs) (apply max xs)])]
  (assert (apply = (map cohort reports)) "Source/runtime cohorts differ")
  (assert (= 3 (count (set (map :process reports)))) "Process identities must differ")
  (assert (apply = (map #(mapv (juxt :workload :n :expected) (:rows %)) reports))
          "Workloads/results differ")
  (let [rows (mapv
               (fn [i]
                 (let [row (get-in (first reports) [:rows i])
                       engines (mapv #(get-in % [:rows i :engines]) reports)]
                   {:workload (:workload row) :n (:n row)
                    :reference-ns (span (map #(get-in % [:reference :median-ns]) engines))
                    :fused-ns (span (map #(get-in % [:fused :median-ns]) engines))
                    :speedup (span (map #(/ (get-in % [:reference :median-ns])
                                            (get-in % [:fused :median-ns])) engines))
                    :reference-bytes (span (map #(get-in % [:reference :median-bytes]) engines))
                    :fused-bytes (span (map #(get-in % [:fused :median-bytes]) engines))
                    :allocation-reduction
                    (span (map #(- 1 (/ (get-in % [:fused :median-bytes])
                                         (get-in % [:reference :median-bytes]))) engines))}))
               (range (count (:rows (first reports)))))
        result {:cohort (cohort (first reports)) :reports paths
                :aggregation :ranges-of-process-medians-and-within-process-ratios :rows rows}]
    (io/make-parents "target/interpreter/summary.edn")
    (spit "target/interpreter/summary.edn" (with-out-str (pp/pprint result)))
    (println "workload\tn\treference-ms\tfused-ms\tspeedup\tallocation-reduction-percent")
    (doseq [row rows]
      (println (str/join "\t"
                        [(:workload row) (:n row)
                         (mapv #(/ % 1e6) (:reference-ns row))
                         (mapv #(/ % 1e6) (:fused-ns row))
                         (:speedup row) (mapv #(* 100 %) (:allocation-reduction row))])))))
