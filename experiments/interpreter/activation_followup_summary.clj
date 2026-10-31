(ns interpreter.activation-followup-summary
  (:require [clojure.edn :as edn] [clojure.pprint :as pp]
            [clojure.java.io :as io] [klara.core :as core]))

(let [paths (mapv #(str "target/interpreter/activation-followup-" % ".edn") (range 3))
      reports (mapv #(edn/read-string (slurp %)) paths)
      cohort #(select-keys % [:source-sha256 :java :clojure :jvm-arguments :measurement])
      span (fn [xs] [(apply min xs) (apply max xs)])]
  (assert (apply = (map cohort reports)) "Source/runtime cohorts differ")
  (assert (= 3 (count (set (map :process reports)))))
  (assert (apply = (map #(get-in % [:recovery :logical-frames]) reports)))
  (let [groups {:small-calls #(get % :small-calls) :recovery #(get-in % [:recovery :engines])}
        result {:cohort (cohort (first reports)) :reports paths
                :logical-frames (get-in (first reports) [:recovery :logical-frames])
                :results
                (into {} (for [[name select] groups :let [engines (mapv select reports)]]
                           [name {:activation/node-time
                                  (span (map #(/ (get-in % [:activation :median-ns])
                                                 (get-in % [:nodes :median-ns])) engines))
                                  :engines (into {} (for [e [:nodes :activation]]
                                                      [e {:ns (span (map #(get-in % [e :median-ns]) engines))
                                                          :bytes (span (map #(get-in % [e :median-bytes]) engines))}]))}]))}]
    (io/make-parents "target/interpreter/activation-followup-summary.edn")
    (spit "target/interpreter/activation-followup-summary.edn" (with-out-str (pp/pprint result)))
    (pp/pprint (:results result))
    (doseq [[path hash] (get-in result [:cohort :source-sha256])]
      (assert (= hash (core/sha256 (slurp path))) (str "recorded source changed: " path)))))
