;; rules: L3.effect.time
;; expect: [true 42 true]
(ns tm (:require [klara.time :as time] [klara.effect :refer [handle]] [klara.job :as job]))
[(number? (time/now))
 (handle {:time/now (fn [k] (k 42))} (time/now))
 (number? (:value (job/run {} (fn [] (time/now)))))]
