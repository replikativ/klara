(ns interpreter.activation-summary
  (:require [clojure.edn :as edn] [clojure.pprint :as pp]
            [clojure.java.io :as io] [clojure.string :as str]))

(let [paths (mapv #(str "target/interpreter/activation-" % ".edn") (range 3))
      reports (mapv #(edn/read-string (slurp %)) paths)
      cohort #(select-keys % [:source-sha256 :java :clojure :jvm-arguments :os :measurement])
      span (fn [xs] [(apply min xs) (apply max xs)])]
  (assert (apply = (map cohort reports)) "Source/runtime cohorts differ")
  (assert (= 3 (count (set (map :process reports)))) "Need independent process IDs")
  (assert (apply = (map #(mapv (juxt :workload :n :expected) (:rows %)) reports)))
  (let [rows
        (mapv (fn [i]
                (let [r (get-in (first reports) [:rows i]) values (mapv #(get-in % [:rows i]) reports)]
                  {:workload (:workload r) :n (:n r)
                   :speedup (span (map #(/ (get-in % [:engines :nodes :median-ns])
                                           (get-in % [:engines :activation :median-ns])) values))
                   :allocation-ratio (span (map #(/ (get-in % [:engines :activation :median-bytes])
                                                    (get-in % [:engines :nodes :median-bytes])) values))
                   :engines (into {} (for [e [:nodes :activation]]
                                       [e {:ns (span (map #(get-in % [:engines e :median-ns]) values))
                                           :bytes (span (map #(get-in % [:engines e :median-bytes]) values))
                                           :prepare-ns (span (map #(get-in % [:preparation e :median-ns]) values))
                                           :prepare-bytes (span (map #(get-in % [:preparation e :median-bytes]) values))}]))}))
              (range (count (:rows (first reports)))))
        snapshots (mapv :snapshots reports)
        _ (assert (apply = (map :logical-frames snapshots)))
        snapshot-summary {:logical-frames (:logical-frames (first snapshots))
                          :engines (into {} (for [e [:nodes :activation]]
                                              [e {:ns (span (map #(get-in % [:engines e :median-ns]) snapshots))
                                                  :bytes (span (map #(get-in % [:engines e :median-bytes]) snapshots))}]))}
        result {:cohort (cohort (first reports)) :reports paths :rows rows :snapshots snapshot-summary
                :aggregation :ranges-of-process-medians-and-within-process-ratios}]
    (io/make-parents "target/interpreter/activation-summary.edn")
    (spit "target/interpreter/activation-summary.edn" (with-out-str (pp/pprint result)))
    (println "workload\tn\tspeedup\tactivation/node-bytes\tnode-ns\tactivation-ns\tnode-prepare-ns\tactivation-prepare-ns")
    (doseq [r rows]
      (println (str/join "\t" [(:workload r) (:n r) (:speedup r) (:allocation-ratio r)
                                  (get-in r [:engines :nodes :ns]) (get-in r [:engines :activation :ns])
                                  (get-in r [:engines :nodes :prepare-ns])
                                  (get-in r [:engines :activation :prepare-ns])])) )
    (println :snapshot-pair snapshot-summary)))
