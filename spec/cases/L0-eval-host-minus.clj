;; rules: L0.eval.host
;; expect: [9223372036854775804 :overflow :overflow]
(defn sub [a b] (- a b))
[(sub -4 -9223372036854775808)
 (try (sub 0 -9223372036854775808) (catch ArithmeticException e :overflow))
 (try (- 9223372036854775807 -1) (catch ArithmeticException e :overflow))]
