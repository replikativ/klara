;; rules: L3.effect.host-boundary
;; expect: [1 9 25]
(mapv (fn [x] (* x x)) (filter odd? (range 6)))
