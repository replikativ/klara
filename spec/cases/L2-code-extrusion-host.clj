;; rules: L2.code.extrusion
;; expect: [3 5]
(ns eh (:require [klara.stage :refer [code esc run]] [klara.code :as c]))
;; the body function is called through host apply and mapv: still inside the construction
(def f (run (c/fn* 2 (fn [self & ps] (apply (fn [a b] (code (+ (esc a) (esc b)))) ps)))))
(def g (run (c/fn* 1 (fn [self x] (first (mapv (fn [_] (code (inc (esc x)))) [1]))))))
[(f 1 2) (g 4)]
