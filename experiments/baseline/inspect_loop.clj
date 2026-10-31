(ns baseline.inspect-loop
  "Dump experimental classes for javap; not a performance measurement."
  (:require [baseline.loop-emission :as experiment]
            [baseline.investment :as investment]
            [klara.compile.baseline :as baseline] [klara.expand :as expand]
            [klara.world :as world]
            [clojure.java.io :as io] [clojure.pprint :as pp]))

(defn -main [& _]
  (let [directory "target/investment/classes"
        _ (.mkdirs (io/file directory))
        classes (binding [*compile-files* true *compile-path* directory]
                  (assoc (into {} (for [[label direct?] [[:letfn false] [:loop true]]
                                 :let [exe (experiment/executable (get-in investment/workloads [:loop :form]) direct? false)]]
                             [label (.getName (class (:invoke exe)))]))
                         :production (.getName (class (:invoke (baseline/compile-source
                                                                 world/empty-root
                                                                 (expand/expand-expr (get-in investment/workloads [:loop :form]) world/empty-root)
                                                                 {}))))))]
    (spit "target/investment/classes.edn" (with-out-str (pp/pprint classes)))
    (prn classes))
  (shutdown-agents))
