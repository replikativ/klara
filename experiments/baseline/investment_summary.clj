(ns baseline.investment-summary
  (:require [clojure.edn :as edn] [clojure.pprint :as pp]
            [clojure.java.io :as io] [clojure.string :as str]))

(defn span [xs] [(apply min xs) (apply max xs)])
(defn break-even [cost before after]
  (when (and cost before after)
    (let [saving (- before after)]
      (if (pos? saving)
        {:calls (long (Math/ceil (/ cost saving))) :saving-ns saving}
        {:no-measured-payback true :saving-ns saving}))))

(defn -main [& _]
  (let [paths (mapv #(str "target/investment/run-" % ".edn") (range 3))
        reports (mapv #(edn/read-string (slurp %)) paths)
        cohort #(select-keys % [:source-sha256 :java :vm :vendor :clojure :sci :jvm-arguments :measurement])
        shape #(mapv (fn [w] [(:workload w) (:source w)
                               (mapv (fn [r] [(:n r) (:expected-id r) (set (keys (:engines r)))]) (:rows w))]) (:workloads %))]
    (assert (apply = (map cohort reports)) "Source/runtime cohorts differ")
    (assert (= 3 (count (set (map :process reports)))))
    (assert (apply = (map shape reports)) "Workloads/results/coverage differ")
    (let [rows
          (vec (for [wi (range (count (:workloads (first reports))))
                     ri (range (count (get-in (first reports) [:workloads wi :rows])))
                     :let [workloads (mapv #(get-in % [:workloads wi]) reports)
                           rs (mapv #(get-in % [:rows ri]) workloads) r (first rs)]]
                 {:workload (:workload (first workloads)) :n (:n r)
                  :engines (into {} (for [e (keys (:engines r))]
                                     [e {:ns (span (map #(get-in % [:engines e :median-ns]) rs))
                                         :bytes (span (map #(get-in % [:engines e :median-bytes]) rs))}]))
                  ;; Paired within a JVM. This is an estimate using later
                  ;; measured costs, not a replay of an online investment.
                  :baseline-payback (mapv (fn [w r]
                                            (break-even (get-in w [:preparation :baseline :total-ns])
                                                        (get-in r [:engines :t0 :median-ns])
                                                        (get-in r [:engines :baseline :median-ns]))) workloads rs)
                  :optimizing-over-baseline-payback
                  (mapv (fn [w r]
                          (break-even (get-in w [:preparation :optimizing :total-ns])
                                      (get-in r [:engines :baseline :median-ns])
                                      (get-in r [:engines :optimizing :median-ns]))) workloads rs)}))
          result {:cohort (cohort (first reports)) :reports paths :rows rows
                  :preparation (mapv (fn [wi]
                                       {:workload (get-in (first reports) [:workloads wi :workload])
                                        :processes (mapv #(get-in % [:workloads wi :preparation]) reports)})
                                     (range (count (:workloads (first reports)))))
                  :entry-studies (mapv (fn [r] (into {} (keep (fn [w] (when (:entry-studies w)
                                                                                     [(:workload w) (:entry-studies w)]))) (:workloads r))) reports)
                  :cache-stats (mapv (fn [r] (into {} (map (juxt :workload :cache-stats)) (:workloads r))) reports)
                  :repeated-preparation (mapv :repeated-preparation reports)
                  :budgets (mapv :budgets reports)}
          output "target/investment/summary.edn"]
      (io/make-parents output) (spit output (with-out-str (pp/pprint result)))
      (println "workload\tn\tengine\tmin-us\tmax-us\tmin-bytes\tmax-bytes")
      (doseq [r rows [e d] (sort-by key (:engines r))]
        (println (str/join "\t" (concat [(:workload r) (:n r) e]
                                          (map #(/ % 1000.0) (:ns d)) (:bytes d)))))
    (shutdown-agents))))
