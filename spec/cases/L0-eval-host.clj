;; rules: L0.eval.host L0.surface.resolve
;; expect: :caught
(try (/ 1 0) (catch ArithmeticException e :caught))
