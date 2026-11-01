;; rules: L0.surface.defrecord
;; expect: [1 2 {:x 1 :y nil} true false true false 5]
(ns rec)
(defrecord Point [x y])
(def p (->Point 1 2))
(def q (map->Point {:x 1}))
(def v (volatile! 2))
(vswap! v + 3)
[(:x p) (:y p) (into {} q)
 (instance? Point p)
 (= q {:x 1 :y nil})                ; a record is not equal to a map, as in Clojure
 (= (assoc p :y 3) (->Point 1 3))
 (instance? Point (dissoc p :x))    ; dissociating a field gives a map
 @v]
