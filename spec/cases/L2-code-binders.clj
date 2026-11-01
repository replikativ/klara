;; rules: L2.code.binders
;; expect: [7 120 [:fn :fn] :L2.code.binders]
(ns cb (:require [klara.stage :refer [code esc run lift]] [klara.code :as c]))
;; a two-parameter function built without naming its parameters
(def add (run (c/fn* 2 (fn [self a b] (code (+ (esc a) (esc b)))))))
;; factorial as a loop: (loop [n 5 acc 1] (if (zero? n) acc (recur (dec n) (* acc n))))
(def fact-code
  (c/loop* [(lift 5) (lift 1)]
    (fn [[n acc] recur]
      (code (if (zero? (esc n)) (esc acc) (esc (recur (code (dec (esc n))) (code (* (esc acc) (esc n))))))))))
;; the names are fresh: two functions built the same way do not collide
(def nested (c/fn* 1 (fn [s x] (c/fn* 1 (fn [s2 y] (code (+ (esc x) (esc y))))))))
[(add 3 4) (run fact-code) [(:op (c/view nested)) (:op (c/view (:body (c/view nested))))]
 (try (c/fn* 1 (fn [s x] 42)) (catch Exception e (:rule (ex-data e))))]
