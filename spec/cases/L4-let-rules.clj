;; rules: L4.check.let-value L4.check.let-app L4.check.alpha
;; expect: [:ready :ready :rejected]
(ns k3 (:require [klara.stage :refer [code]] [klara.compiler :as compiler]))
(defn f [y] (inc y))
[(:status (compiler/prepare (code (fn [a] (let [b 1] (+ a b)))) {:recipe (fn [_] (code (fn [z] (+ z 1))))}))
 (:status (compiler/prepare (code (fn [a] ((fn [x] (* x 2)) (f a)))) {:recipe (fn [_] (code (fn [z] (let [w (f z)] (* w 2)))))}))
 (:status (compiler/prepare (code (fn [a] (let [unused (f a)] 1))) {:recipe (fn [_] (code (fn [z] 1)))}))]
