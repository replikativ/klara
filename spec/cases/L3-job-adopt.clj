;; rules: L3.job.adopt L3.job.adopted
;; expect-rule: :L3.job.adopted
(ns e8 (:require [klara.job :as job]))
(def price 10)
(def o (job/run {} (fn [] (def price 7) :ok)))
(job/adopt! o)
(def after price)
(job/adopt! o)
