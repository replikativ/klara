(require '[klara.core] '[clojure.edn :as edn] '[clojure.java.io :as io] '[clojure.pprint :as pp])
(let [reports (mapv #(edn/read-string (slurp (str "target/entry/final-" % ".edn"))) (range 3))
      median (fn [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
      aggregate (fn [xs] {:process-medians (vec xs) :median (median xs) :range [(apply min xs) (apply max xs)]})
      rows (fn [section]
             (mapv (fn [i]
                     (let [rs (mapv #(get-in % [section i]) reports)]
                       (merge (select-keys (first rs) [:cache :arguments :expected :diagnostics])
                              {:metrics (into {} (for [metric [:wall-ns-per-call :cpu-ns-per-call :bytes-per-call]]
                                                   [metric (into {} (for [mode [:reference :planned]]
                                                                      [mode (aggregate (mapv #(get-in % [:medians mode metric]) rs))]))]))})))
                   (range (count (section (first reports))))))
      observations (fn [key] (into {} (for [metric [:wall-ns-per-call :cpu-ns-per-call :bytes-per-call]]
                                       [metric (aggregate (mapv #(median (mapv metric (key %))) reports))])))
      summary {:selector (rows :selector) :full-calls (rows :full-calls)
               :direct-site (observations :direct-site) :evidence-site (observations :evidence-site)
               :java (mapv :java reports) :source-sha256 (:source-sha256 (first reports))}]
  (assert (apply = (map :source-sha256 reports)))
  (doseq [[path sha] (:source-sha256 summary)] (assert (= sha (klara.core/sha256 (slurp path))) path))
  (doseq [section [:selector :full-calls] i (range (count (section (first reports))))]
    (assert (apply = (map #(get-in % [section i :expected]) reports))))
  (spit "target/entry/final-summary.edn" (with-out-str (pp/pprint summary)))
  (doseq [section [:selector :full-calls]]
    (println section)
    (doseq [r (section summary)]
      (prn (:cache r) (:arguments r)
           (into {} (for [m [:wall-ns-per-call :bytes-per-call]]
                      [m (into {} (for [mode [:reference :planned]]
                                   [mode (select-keys (get-in r [:metrics m mode]) [:median :range])]))])))))
  (prn :direct (:direct-site summary) :evidence (:evidence-site summary))
  (prn :diagnostics (mapv #(select-keys % [:cache :arguments :diagnostics]) (:selector summary))))
