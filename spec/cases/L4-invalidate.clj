;; rules: L4.exec.valid
;; expect: [2 101]
(ns k8 (:require [klara.compiler :as compiler]))
(defn score [x] (+ x 1))
(compiler/optimize! 'k8/score)
(def a (score 1))
(defn score [x] (+ x 100))
[a (score 1)]
