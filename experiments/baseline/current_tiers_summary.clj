(ns baseline.current-tiers-summary
  (:require [clojure.edn :as edn] [clojure.pprint :as pp]
            [clojure.java.io :as io] [clojure.string :as str]))

(let [paths (mapv #(str "target/baseline/current-tiers-" % ".edn") (range 3))
      reports (mapv #(edn/read-string (slurp %)) paths)
      cohort #(select-keys % [:source-sha256 :java :clojure :sci :jvm-arguments :measurement])
      span (fn [xs] [(apply min xs) (apply max xs)])]
  (assert (apply = (map cohort reports)) "Source/runtime cohorts differ")
  (assert (= 3 (count (set (map :process reports)))))
  (assert (apply = (map #(mapv (juxt :workload :n :expected :unsupported) (:rows %)) reports)))
  (let [rows
        (mapv (fn [i]
                (let [r (get-in (first reports) [:rows i]) values (mapv #(get-in % [:rows i :engines]) reports)]
                  {:workload (:workload r) :n (:n r) :unsupported (:unsupported r)
                   :engines (into {} (for [e (keys (:engines r))]
                                       [e {:ns (span (map #(get-in % [e :median-ns]) values))
                                           :bytes (span (map #(get-in % [e :median-bytes]) values))}]))}))
              (range (count (:rows (first reports)))))
        result {:cohort (cohort (first reports)) :reports paths
                :aggregation :ranges-of-process-medians :rows rows}]
    (io/make-parents "target/baseline/current-tiers-summary.edn")
    (spit "target/baseline/current-tiers-summary.edn" (with-out-str (pp/pprint result)))
    (println "workload\tn\tengine\tmin-us\tmax-us\tmin-bytes\tmax-bytes")
    (doseq [r rows [e d] (:engines r)]
      (println (str/join "\t" (concat [(:workload r) (:n r) e]
                                         (map #(/ % 1000.0) (:ns d)) (:bytes d)))))))
