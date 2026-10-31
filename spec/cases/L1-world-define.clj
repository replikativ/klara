;; rules: L1.world.define L1.session.publish L1.session.current
;; expect: [[20 50] 50]
(ns c3 (:require [klara.world :as world]))
(def rate 2)
(defn price [x] (* x rate))
(def proposal (world/define (world/current) 'c3/rate 5))
(def a [(price 10) (world/in proposal price 10)])
(world/publish! proposal)
(world/advance)
[a (price 10)]
