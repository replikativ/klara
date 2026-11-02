;; rules: L3.account.foreign
;; expect: [:L3.account.foreign {:eur 1 :steps 1000} {:eur 2}]
(ns acf (:require [klara.account :as a] [klara.job :as job]))
(a/mint! {:eur 2})
(let [t (a/take {:eur 1})
      captured (job/run {} (fn [] (a/balance t)))
      moved (job/run {:budget (a/take {:eur 1 :steps 1000})} (fn [] (a/wallet)))]
  (a/put t)
  [(get-in captured [:error :rule]) (get-in moved [:receipt :granted]) (a/wallet)])
