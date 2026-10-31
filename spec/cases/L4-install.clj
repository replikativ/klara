;; rules: L4.exec.install L4.retain.dispatch L4.exec.explain L4.lower.calls
;; expect: [[11 :compiled] 16]
(ns k7 (:require [klara.compiler :as compiler]))
(defn helper [x] (* 2 x))
(defn score [x] (+ (helper x) 1))
(compiler/optimize! 'k7/score)
(def r1 [(score 5) (:last-path (compiler/explain score))])
(defn helper [x] (* 3 x))
[r1 (score 5)]
