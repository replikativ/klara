;; rules: L1.context.advance
;; expect-rule: :L1.context.advance
(ns c7 (:require [klara.world :as world]))
(world/in (world/current) (fn [] (world/advance)))
