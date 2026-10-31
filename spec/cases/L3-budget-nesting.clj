;; rules: L3.budget.nesting
;; expect: [:exhausted true]
(ns e10 (:require [klara.job :as job]))
(defn spin [n] (if (= n 0) :finished (spin (dec n))))
(def outer (job/run {:budget {:steps 1000}} (fn [] (:status (job/run {:budget {:steps 100000}} (fn [] (spin 100000)))))))
[(:value outer) (<= (:steps (:spent outer)) 1000)]
