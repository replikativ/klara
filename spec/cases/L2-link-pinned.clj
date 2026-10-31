;; rules: L2.link.pinned
;; expect: 11
(ns s11 (:require [klara.stage :refer [code esc run]] [klara.world :as world]))
(def k 1)
(def c (code (+ 10 (esc (world/link (world/current) 's11/k)))))
(def k 2)
(run c)
