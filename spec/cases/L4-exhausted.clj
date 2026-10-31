;; rules: L4.check.exhausted
;; expect: :exhausted
(ns k4 (:require [klara.stage :refer [code]] [klara.compiler :as compiler]))
(defn power [n x] (if (= n 0) 1 (* x (power (dec n) x))))
(:status (compiler/prepare (code (fn [x] (power 30 x))) {:recipe (fn [_] (code (fn [x] (* x (* x 1))))) :budget {:steps 40}}))
