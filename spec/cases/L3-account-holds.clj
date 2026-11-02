;; rules: L3.account.holds
;; expect: [true false true {:db 2}]
(ns ach (:require [klara.account :as a]))
(a/mint! {:db 3})
(let [reader (a/take {:db 1})]
  [(a/holds? reader {:db 1}) (a/holds? reader {:db 3}) (a/holds? reader {:db 1}) (a/wallet)])
