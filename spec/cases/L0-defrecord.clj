;; rules: L0.surface.defrecord
;; expect: [1 2 {:x 1 :y nil} rec/Point 5]
(ns rec)
(defrecord Point [x y])
(def p (->Point 1 2))
(def q (map->Point {:x 1}))
(def v (volatile! 2))
(vswap! v + 3)
[(:x p) (:y p) q (:klara/record (meta p)) @v]
