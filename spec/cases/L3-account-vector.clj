;; rules: L3.account.vector
;; expect-rule: :L3.account.vector
(ns acv (:require [klara.account :as a]))
(a/mint! {:eur 0.5})
