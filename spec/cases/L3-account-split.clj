;; rules: L3.account.split
;; expect: [{:eur 1/3} {:eur 2/3} {:eur 1}]
(ns acs (:require [klara.account :as a]))
(a/mint! {:eur 1})
(let [[t1 t2] (a/split (a/take {:eur 1}) {:eur 1/3})
      b [(a/balance t1) (a/balance t2)]
      t (a/join t1 t2)]
  (conj b (a/balance t)))
