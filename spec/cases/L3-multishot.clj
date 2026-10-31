;; rules: L3.cont.multishot
;; expect: (:heads :tails)
(ns e2 (:require [klara.effect :refer [perform handle]]))
(handle {:flip (fn [k] (concat (k true) (k false)))}
  [(if (perform :flip) :heads :tails)])
