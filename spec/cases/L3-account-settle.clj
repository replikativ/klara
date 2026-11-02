;; rules: L3.account.settle L3.budget.exhausted
;; expect: [:exhausted {:eur 3/2} {:eur 19/2}]
(ns acse (:require [klara.account :as a] [klara.job :as job]))
(a/mint! {:eur 10})
(defn spin [] (loop [] (recur)))
(let [o (job/run {:budget {:steps 100 :eur 2}}
                 (fn [] (a/spend! {:eur 1/2}) (let [t (a/take {:eur 1})] (spin))))]
  [(:status o) (dissoc (get-in o [:receipt :returned]) :steps) (a/wallet)])
