;; rules: L4.profile.record L4.profile.snapshot
;; expect: [10 ["java.lang.Long"] [:unstable] 3 [[:value 5]] [7 3] 10]
(ns pr (:require [klara.profile :as profile]))
(defn sq [x] (* x x))
(defn g [x] (* x x))
(defn sum-squares [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (sq i))) acc)))
(defn parity [y] (if (odd? y) :odd :even))
(sum-squares 10)
(dotimes [_ 3] (g 5))
(dotimes [i 10] (parity (if (< i 7) 1 2)))
(def p (profile/snapshot sq))
(def q (profile/snapshot g))
(def b (profile/snapshot parity))
(def l (profile/snapshot sum-squares))
[(:count (:entries p)) (mapv #(.getName %) (:classes (:entries p))) (:stable (:entries p))
 (:count (:entries q)) (:stable (:entries q))
 [(:then (first (:branches b))) (:else (first (:branches b)))]
 (apply max (map :count (:calls l)))]
