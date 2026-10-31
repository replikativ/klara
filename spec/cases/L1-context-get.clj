;; rules: L1.context.get L1.context.call-based L1.context.mint L1.slice.resolve
;; expect: [20 20 30]
(ns c2 (:require [klara.world :as world]))
(def rate 2)
(defn price [x] (* x rate))
(defn make-pricer [] (fn [x] (price x)))
(def old-price (world/get (world/current) 'c2/price))
(def old-maker (world/get (world/current) 'c2/make-pricer))
(def rate 3)
(def made (old-maker))
[(old-price 10) (made 10) ((make-pricer) 10)]
