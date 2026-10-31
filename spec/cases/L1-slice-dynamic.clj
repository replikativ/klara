;; rules: L1.slice.dynamic L1.slice.footprint
;; expect: [#{c8/plain c8/a} nil]
(ns c8 (:require [klara.world :as world] [klara.stage :refer [code run]]))
(def a 1)
(defn plain [] a)
(defn dynamic [] (run (code a)))
[(world/footprint (world/get (world/current) 'c8/plain)) (world/footprint (world/get (world/current) 'c8/dynamic))]
