;; rules: L4.lower.steps
;; expect: [32 :done :exhausted]
(ns k11 (:require [klara.compiler :as compiler] [klara.job :as job]))
(defn power [n x] (if (= n 0) 1 (* x (power (dec n) x))))
(def p5 (compiler/specialize power {0 5}))
[(p5 2) (:status (job/run {:budget {:steps 3}} (fn [] (p5 2)))) (:status (job/run {:budget {:steps 3}} (fn [] (power 5 2))))]
