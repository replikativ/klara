;; rules: L3.account.token
;; expect: [{:eur 1} {:eur 3/4} {:eur 19/4} true false]
(ns act (:require [klara.account :as a] [klara.stage :as st]))
(a/mint! {:eur 5})
(let [t (a/take {:eur 1})
      b1 (a/balance t)
      t (a/spend t {:eur 1/4})
      b2 (a/balance t)]
  (a/put t)
  [b1 b2 (a/wallet) (a/token? t) (st/liftable? t)])
