;; rules: L2.link.late
;; expect: [2 1]
(ns s10 (:require [klara.stage :refer [code run]] [klara.world :as world]))
(def k 1)
(def c (code k))
(def old (world/current))
(def k 2)
[(run c) (world/in old (fn [] (run c)))]
