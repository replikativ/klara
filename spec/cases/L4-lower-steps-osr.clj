;; rules: L4.lower.steps L4.exec.osr L3.budget.steps
;; expect: [true true]
(ns k-steps-osr (:require [klara.compiler :as compiler] [klara.effect :refer [perform handle]] [klara.job :as job]))
;; a compiled loop leaves at every iteration (its callee performs) and is
;; re-entered by OSR at the next one: each iteration costs one step, as
;; interpreted
(defn ask [i] (perform :ask i))
(defn gen [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (ask i))) acc)))
(defn run [] (job/run {:budget {:steps 100000}} (fn [] (handle {:ask (fn [k i] (k i))} (gen 200)))))
(def interpreted (run))
(compiler/optimize! 'k-steps-osr/gen)
(def compiled (run))
[(= (:value interpreted) (:value compiled))
 (= (:spent interpreted) (:spent compiled))]
