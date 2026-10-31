;; rules: L3.budget.steps L3.budget.exhausted L3.job.resume
;; expect: [:exhausted {:steps 50} :finished]
(ns e9 (:require [klara.job :as job]))
(defn spin [n] (if (= n 0) :finished (spin (dec n))))
(def o (job/run {:budget {:steps 50}} (fn [] (spin 1000))))
[(:status o) (:spent o) (:value (job/resume o {:steps 100000}))]
