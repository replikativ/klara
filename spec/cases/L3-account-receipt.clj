;; rules: L3.account.receipt L3.job.outcome
;; expect: [[:grant :consume :return] true {:steps 1 :eur 1}]
(ns acr (:require [klara.account :as a] [klara.job :as job]))
(a/mint! {:eur 3})
(let [o (job/run {:budget {:eur 3 :steps 100}} (fn [] (a/spend! {:eur 1})))
      r (:receipt o)]
  [(mapv :kind (:postings r))
   (= (:granted r) (merge-with + (:spent r) (:returned r)))
   (:spent o)])
