(ns interpreter.mutable-summary
  (:require [clojure.edn :as edn] [clojure.java.io :as io]
            [clojure.pprint :as pp] [clojure.string :as str]))

(let [paths (mapv #(str "target/interpreter/mutable-" % ".edn") (range 3))
      reports (mapv #(edn/read-string (slurp %)) paths)
      cohort #(select-keys % [:source-sha256 :java :clojure :jvm-arguments :measurement])
      span (fn [xs] [(apply min xs) (apply max xs)])]
  (assert (apply = (map cohort reports)) "Mixed source/runtime cohorts")
  (assert (= 3 (count (set (map :process reports)))))
  (assert (apply = (map #(mapv (juxt :workload :n :expected) (:rows %)) reports)))
  (let [rows
        (mapv (fn [i]
                (let [row (get-in (first reports) [:rows i])
                      engines (mapv #(get-in % [:rows i :engines]) reports)]
                  {:workload (:workload row) :n (:n row)
                   :speedup (span (map #(/ (get-in % [:t0 :median-ns])
                                           (get-in % [:mutable :median-ns])) engines))
                   :allocation-reduction (span (map #(- 1 (/ (get-in % [:mutable :median-bytes])
                                                            (get-in % [:t0 :median-bytes]))) engines))
                   :engines (into {} (for [engine [:clojure :t0 :mutable]]
                                       [engine {:ns (span (map #(get-in % [engine :median-ns]) engines))
                                                :bytes (span (map #(get-in % [engine :median-bytes]) engines))}]))}))
              (range (count (:rows (first reports)))))
        result {:cohort (cohort (first reports)) :reports paths
                :aggregation :ranges-of-process-medians-and-within-process-ratios :rows rows}]
    (io/make-parents "target/interpreter/mutable-summary.edn")
    (spit "target/interpreter/mutable-summary.edn" (with-out-str (pp/pprint result)))
    (println "workload\tn\tspeedup\tallocation-reduction-percent\tt0-ns\tmutable-ns\tclojure-ns")
    (doseq [r rows]
      (println (str/join "\t" [(:workload r) (:n r) (:speedup r)
                                  (mapv #(* 100 %) (:allocation-reduction r))
                                  (get-in r [:engines :t0 :ns]) (get-in r [:engines :mutable :ns])
                                  (get-in r [:engines :clojure :ns])])))))
