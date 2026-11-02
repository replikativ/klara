;; rules: L3.account.mint
;; expect: [:failed :L3.account.mint]
(ns acm (:require [klara.account :as a] [klara.job :as job]))
(let [o (job/run {} (fn [] (a/mint! {:eur 1})))]
  [(:status o) (get-in o [:error :rule])])
