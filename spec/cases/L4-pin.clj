;; rules: L4.pin.links
;; expect: [[] 10]
(ns k10 (:require [klara.stage :refer [code]] [klara.compiler :as compiler] [klara.world :as world]))
(defn helper [x] (* 2 x))
(def o (compiler/prepare (compiler/pin (code (fn [x] (helper x))) (world/current)) {:recipe compiler/as-is}))
(defn helper [x] (* 3 x))
(def f (compiler/executable o))
[(:premises o) (f 5)]
