;; rules: L3.job.run L3.job.outcome L3.job.define L3.job.print L3.job.discard
;; expect: [:done 7 10 [[:io/print "hi\n"]]]
(ns e6 (:require [klara.job :as job]))
(def price 10)
(def o (job/run {} (fn [] (def price 7) (println "hi") price)))
[(:status o) (:value o) price (:intents o)]
