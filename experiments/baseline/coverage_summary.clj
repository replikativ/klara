(ns baseline.coverage-summary
  (:require [clojure.edn :as edn] [clojure.pprint :as pp]
            [clojure.java.io :as io] [clojure.string :as str]))

(defn span [xs] [(apply min xs) (apply max xs)])
(defn -main [& _]
  (let [reports (mapv #(edn/read-string (slurp (str "target/coverage/run-" % ".edn"))) (range 3))
        cohort #(select-keys % [:java :source-sha256 :jvm-arguments :measurement])
        shape #(mapv (fn [w] [(:workload w) (:source w)
                              (mapv (fn [r] [(:n r) (:expected-id r) (set (keys (:engines r)))]) (:rows w))]) (:workloads %))]
    (assert (apply = (map cohort reports)))
    (assert (apply = (map shape reports)))
    (assert (= #{0 1 2} (set (map :process reports))))
    (let [rows (vec (for [wi (range (count (:workloads (first reports))))
                         ri (range (count (get-in (first reports) [:workloads wi :rows])))
                         :let [ws (mapv #(get-in % [:workloads wi]) reports)
                               rs (mapv #(get-in % [:rows ri]) ws)]]
                     {:workload (:workload (first ws)) :n (:n (first rs))
                      :preparation (mapv :preparation ws)
                      :engines (into {} (for [e (keys (:engines (first rs)))]
                                         [e {:ns (span (map #(get-in % [:engines e :median-ns]) rs))
                                             :bytes (span (map #(get-in % [:engines e :median-bytes]) rs))}]))}))
          result {:cohort (cohort (first reports)) :rows rows
                  :mutual-support (mapv :mutual-support reports)
                  :cache-stats (mapv #(mapv (juxt :workload :cache-stats) (:workloads %)) reports)}]
      (io/make-parents "target/coverage/summary.edn")
      (spit "target/coverage/summary.edn" (with-out-str (pp/pprint result)))
      (println "workload\tn\tengine\tmin-us\tmax-us\tmin-bytes\tmax-bytes")
      (doseq [r rows [e d] (sort-by key (:engines r))]
        (println (str/join "\t" (concat [(:workload r) (:n r) e] (map #(/ % 1000.0) (:ns d)) (:bytes d)))))
      (prn :mutual-support (:mutual-support result))))
  (shutdown-agents))
