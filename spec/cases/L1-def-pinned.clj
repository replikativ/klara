;; rules: L1.def.pinned
;; expect-rule: :L1.def.pinned
(ns c4 (:require [klara.world :as world]))
(world/in (world/current) (fn [] (def x 1)))
