;; rules: L3.account.wallet L3.account.vector
;; expect: [{:eur 7/2} {:eur 2 :steps 1000} {:eur 3/2 :steps 999}]
(ns acw (:require [klara.account :as a] [klara.job :as job]))
(a/mint! {:eur 4.5M :db 0})
(a/spend! {:eur 1})
(let [w (a/wallet)
      o (job/run {:budget {:eur 2 :steps 1000}} (fn [] (a/spend! {:eur 1/2}) (a/wallet)))]
  [w (get-in o [:receipt :granted]) (:value o)])
