;; rules: L3.affine.reuse L3.cont.multishot
;; expect: [:spent :L3.affine.reuse]
(ns acu (:require [klara.account :as a] [klara.effect :refer [perform handle]]))
(a/mint! {:eur 2})
(def t (a/take {:eur 1}))
;; the continuation may be resumed twice; only the second use of t fails
(handle {:twice (fn [k] [(k nil) (try (k nil) (catch clojure.lang.ExceptionInfo e (:rule (ex-data e))))])}
  (perform :twice)
  (a/put t)
  :spent)
