;; rules: L0.surface.transient
;; expect: [[1 2 3] true {:a 1} [1 2]]
(ns tr)
(def t (transient [1]))
[(persistent! (reduce conj! (transient []) [1 2 3]))
 (= t [1])
 (persistent! (assoc! (transient {}) :a 1))
 (let [v (transient [1 2 3])] (persistent! (pop! v)))]
