;; rules: L2.code.csp L2.lift.values L2.lift.preserves
;; expect: [6 true]
(ns s2 (:require [klara.stage :refer [code run lift]]))
(def v [1 {:a 2}])
[((run (let [k 5] (code (fn [y] (+ y k))))) 1) (identical? v (run (lift v)))]
