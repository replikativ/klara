;; rules: L1.def.read-your-writes
;; expect: [3 [1 2 3]]
(ns hc)
(def seen [])
(mapv (fn [x] (def seen (conj seen x))) [1 2 3])
[(count seen) seen]
