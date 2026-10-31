;; rules: L1.context.top L1.context.resolve L1.context.call-open L1.def.effect L1.def.read-your-writes L1.world.definition
;; expect: [20 30]
(def rate 2)
(defn price [x] (* x rate))
(def before (price 10))
(def rate 3)
[before (price 10)]
