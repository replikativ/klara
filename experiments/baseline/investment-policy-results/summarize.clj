(require '[klara.core] '[baseline.investment-policy] '[baseline.campaign-summary :as campaign-summary]
         '[clojure.edn :as edn] '[clojure.pprint :as pp])
(let [reports (mapv #(edn/read-string (slurp (str "target/investment-policy/final-policy-" % ".edn"))) (range 3))
      span (fn [xs] (let [ys (vec (sort xs))] {:min (first ys) :median (nth ys 1) :max (last ys)}))
      rows (vec (for [workload (map :id baseline.investment-policy/workloads) mode baseline.investment-policy/modes]
                  (let [rs (mapv (fn [r] (first (filter #(and (= workload (:workload %)) (= mode (:mode %))) (:rows r)))) reports)]
                    {:workload workload :mode mode
                     :trace-ms (span (map #(/ (:trace-wall-ns %) 1e6) rs))
                     :cpu-ms (span (map #(/ (:trace-cpu-ns %) 1e6) rs))
                     :allocated-bytes (span (map :trace-allocated-bytes rs))
                     :investment-ms (span (map #(/ (:investment-ns %) 1e6) rs))
                     :statuses (mapv #(mapv (fn [i] (select-keys i [:at :status :reason])) (:investments %)) rs)})))
      result {:cohorts (mapv :label reports) :processes 3 :rows rows
              :aggregation :min-median-max-of-complete-process-traces
              :source-sha256 (:source-sha256 (first reports))}]
  (assert (apply = (map :source-sha256 reports)))
  (doseq [[p sha] (:source-sha256 result)] (assert (= sha (klara.core/sha256 (slurp p))) p))
  (spit "target/investment-policy/summary.edn" (with-out-str (pp/pprint result)))
  (doseq [r rows] (prn (:workload r) (:mode r) (:trace-ms r))))
(let [r (campaign-summary/summarize! (mapv #(str "target/compiler-campaign/final-campaign-" % ".edn") (range 3))
                                    "target/compiler-campaign/correctness-investment-summary.edn")]
  (doseq [[p sha] (:source-sha256 r)] (assert (= sha (klara.core/sha256 (slurp p))) p))
  (doseq [p (:preparation r)] (prn (select-keys p [:family :variant :preparation-ms :validation-ms])))
  (doseq [row (:rows r) :when (and (= :enclosed-accumulator (:family row)) (= [1000 4 600000] (:arguments row)))]
    (prn (select-keys row [:family :engine :wall-us :allocated-bytes :estimated-total-ms]))))
