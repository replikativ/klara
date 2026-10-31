;; rules: L3.job.host-mutation
;; expect: :L3.job.host-mutation
(ns e11 (:require [klara.job :as job]))
(def counter (atom 0))
(let [o (job/run {} (fn [] (let [mine (atom 0)] (swap! mine inc) (swap! counter inc))))]
  (get-in o [:error :rule]))
