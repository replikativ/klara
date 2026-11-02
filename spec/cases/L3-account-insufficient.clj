;; rules: L3.account.insufficient
;; expect: [:L3.account.insufficient :L3.account.insufficient {:eur 1}]
(ns aci (:require [klara.account :as a] [klara.job :as job]))
(a/mint! {:eur 1})
(defn rule-of [f] (try (f) (catch clojure.lang.ExceptionInfo e (:rule (ex-data e)))))
[(rule-of #(a/spend! {:eur 2}))
 (rule-of #(job/run {:budget {:eur 2}} (fn [] :never)))
 (a/wallet)]
