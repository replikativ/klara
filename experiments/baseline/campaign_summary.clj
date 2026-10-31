(ns baseline.campaign-summary
  (:require [clojure.edn :as edn] [clojure.java.io :as io] [clojure.pprint :as pp]))

(defn- span [xs scale]
  (let [values (vec (sort (map #(/ (double %) scale) (remove nil? xs))))]
    (when (seq values) {:min (first values) :median (nth values (quot (count values) 2)) :max (peek values)})))

(defn summarize! [paths output]
  (let [reports (mapv #(edn/read-string (slurp %)) paths) template (first reports)
        _ (assert (seq reports))
        _ (assert (apply = (map :source-sha256 reports)))
        rows (vec
               (for [[fi family] (map-indexed vector (:families template))
                     [ci case] (map-indexed vector (:cases family))
                     engine (:engine-order family)]
                 (let [cases (mapv #(get-in % [:families fi :cases ci]) reports)
                       _ (assert (every? #(= (:arguments case) (:arguments %)) cases))]
                   {:family (:id family) :arguments (:arguments case) :engine engine
                    :portfolio-selected (mapv :portfolio-selected cases)
                    :wall-us (span (map #(get-in % [:medians engine :wall-ns-per-call]) cases) 1000)
                    :cpu-us (span (map #(get-in % [:medians engine :cpu-ns-per-call]) cases) 1000)
                    :allocated-bytes (span (map #(get-in % [:medians engine :bytes-per-call]) cases) 1)
                    :estimated-total-ms (into {} (for [h [1 10 1000]]
                                                  [h (span (map #(get-in % [:estimated-total-ns engine h]) cases) 1000000)]))})))
        preparation (vec
                      (for [[fi family] (map-indexed vector (:families template))
                            variant (keys (:preparation family))]
                        (let [ps (mapv #(get-in % [:families fi :preparation variant]) reports)]
                          {:family (:id family) :variant variant :statuses (mapv :status ps)
                           :preparation-ms (span (map #(get-in % [:preparation :wall-ns-per-call]) ps) 1000000)
                           :validation-ms (span (map #(get-in % [:validation :wall-ns-per-call]) ps) 1000000)
                           :installation-ms (span (map #(get-in % [:installation :wall-ns-per-call]) ps) 1000000)})))
        result {:cohorts (mapv :label reports) :files paths :processes (count reports)
                :aggregation :min-median-max-of-process-warm-medians
                :source-sha256 (:source-sha256 template) :preparation preparation :rows rows
                :limits (:limits template)}]
    (io/make-parents output) (spit output (with-out-str (pp/pprint result))) result))

(defn -main [output & paths]
  (let [result (summarize! (vec paths) output)] (prn (select-keys result [:cohorts :processes]))))
