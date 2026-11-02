;; rules: L3.cont.context L3.affine.reuse L3.cont.multishot
;; expect: [{:eur 8} :L3.affine.reuse]
(ns e-cont-context (:require [klara.account :as a] [klara.effect :refer [perform handle]]))
(a/mint! {:eur 10})
;; each resumption spends from the resumer's wallet: twice
(handle {:pick (fn [k] (k 1) (k 2))} (do (perform :pick) (a/spend! {:eur 1})))
(def w (a/wallet))
;; a token captured by the continuation is shared by both resumptions
[w (try (handle {:pick (fn [k] (k 1) (k 2))}
          (let [t (a/take {:eur 1})] (perform :pick) (a/put t)))
        nil
        (catch clojure.lang.ExceptionInfo e (:rule (ex-data e))))]
