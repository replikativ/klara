;; rules: L3.job.intent-limit
;; expect: :L3.job.intent-limit
(ns e12 (:require [klara.job :as job]))
(get-in (job/run {:intent-limit 2} (fn [] (dotimes [i 3] (println i)))) [:error :rule])
