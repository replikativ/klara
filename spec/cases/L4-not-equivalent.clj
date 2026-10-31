;; rules: L4.check.not-equivalent
;; expect: :L4.check.not-equivalent
(ns k2 (:require [klara.stage :refer [code]] [klara.compiler :as compiler]))
(defn power [n x] (if (= n 0) 1 (* x (power (dec n) x))))
(:rule (compiler/prepare (code (fn [x] (power 2 x))) {:recipe (fn [_] (code (fn [x] (* x x))))}))
