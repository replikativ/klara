;; rules: L1.context.in L1.context.current L1.world.value
;; expect: [20 30 true]
(ns c1 (:require [klara.world :as world]))
(def rate 2)
(defn price [x] (* x rate))
(def old (world/current))
(def rate 3)
[(world/in old price 10) (price 10) (= old (world/in old (fn [] (world/current))))]
