(ns interpreter.counted-loop-summary
  (:require [clojure.edn :as edn] [clojure.pprint :as pp] [clojure.string :as str]))
(defn span [xs] [(apply min xs) (apply max xs)])
(defn -main [& _]
  (let [reports (mapv #(edn/read-string (slurp (str "target/counted-loop/process-" % ".edn"))) (range 3))
        cohort #(select-keys % [:source-sha256 :java :clojure :jvm-arguments :measurement])
        _ (assert (apply = (map cohort reports)) "Source/runtime cohorts differ")
        _ (assert (= #{0 1 2} (set (map :process reports))))
        _ (assert (apply = (map #(mapv (fn [w] [(:name w) (:source w) (:forms w)
                                                (mapv (juxt :n :expected) (:rows w))]) (:workloads %)) reports)))
        rows (vec (for [wi (range 2) ni (range 2)
                        :let [w (get-in (first reports) [:workloads wi])
                              row (get-in w [:rows ni])]]
                    {:workload (:name w) :n (:n row)
                     :engines (into {} (for [engine (keys (:engines row))]
                                         [engine {:ns (span (map #(get-in % [:workloads wi :rows ni :engines engine :median-ns]) reports))
                                                  :bytes (span (map #(get-in % [:workloads wi :rows ni :engines engine :median-bytes]) reports))}]))}))
        preparation (into {} (for [wi (range 2) :let [w (get-in (first reports) [:workloads wi])]]
                               [(:name w) (into {} (for [phase (keys (:preparation-ns w))]
                                                    [phase (span (map #(get-in % [:workloads wi :preparation-ns phase]) reports))]))]))
        summary {:cohort (cohort (first reports)) :aggregation :ranges-of-process-medians
                 :model-bootstrap-ns (span (map :model-bootstrap-ns reports))
                 :preparation-ns preparation :rows rows}]
    (spit "target/counted-loop/summary.edn" (with-out-str (pp/pprint summary)))
    (let [tsv (str "workload\tn\tengine\tmin-us\tmax-us\tmin-bytes\tmax-bytes\n"
                   (str/join "\n" (for [row rows [engine stats] (:engines row)]
                                     (str/join "\t" (concat [(:workload row) (:n row) engine]
                                                             (map #(/ % 1000.0) (:ns stats)) (:bytes stats))))) "\n")]
      (spit "target/counted-loop/summary.tsv" tsv)
      (print tsv))))
