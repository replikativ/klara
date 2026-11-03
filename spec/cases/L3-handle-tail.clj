;; rules: L3.handle.deep L3.cont.context L3.budget.steps L3.budget.exhausted L4.profile.record L0.eval.exception
;; expect: [[30 2] true :outer 7 ["klara.runtime.value.Continuation" "java.lang.Long"]]
(ns e-handle-tail
  (:require [klara.effect :refer [perform handle]] [klara.job :as job]
            [klara.profile :as profile] [klara.world :as world]))
;; A clause (fn [k x] (k e)) with an immediate e resumes at once, in tail
;; position. Everything the rule makes observable stays as the rule has it.

;; the clause runs in the handle's world, the continuation in the perform's
(def rate 2)
(def old (world/current))
(def rate 3)
(def worlds (handle {:ask (fn [k x] (k (* x rate)))} (world/in old (fn [] [(perform :ask 10) rate]))))

;; two steps per effect, and the same exhaustion points as a clause that
;; does not resume in tail position
(defn gen [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (perform :next i))) acc)))
(defn tail [n] (handle {:next (fn [k x] (k (* 2 x)))} (gen n)))
(defn non-tail [n] (handle {:next (fn [k x] (let [r (k (* 2 x))] r))} (gen n)))
(defn outcome [f b]
  (let [o (job/run {:budget {:steps b}} (fn [] (f 5)))]
    [(:status o) (:spent o) (if (= :exhausted (:status o)) (:value (job/resume o {:steps 1000})) (:value o))]))
(def same-steps (= (map #(outcome tail %) (range 1 40)) (map #(outcome non-tail %) (range 1 40))))

;; an exception of e is raised where the clause runs: outside the handle,
;; so not caught by a try between the perform and the handle
(defn g [] (try (perform :ask 1) (catch ArithmeticException e :inner)))
(def raised (try (handle {:ask (fn [k x] (k (+ x 9223372036854775807)))} (g))
                 (catch ArithmeticException e :outer)))

;; the clause's profile records each entry with its continuation
(defn clause [k x] (k (* 2 x)))
(handle {:next clause} (gen 7))
(def p (:entries (profile/snapshot clause)))

[worlds same-steps raised (:count p) (mapv #(.getName %) (:classes p))]
