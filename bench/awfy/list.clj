(ns awfy.list
  "Are We Fast Yet? List: building and walking linked records, deep recursion.")

(defrecord Element [val next])

(defn make-list [n] (when (pos? n) (->Element n (make-list (dec n)))))

(defn shorter? [x y]
  (loop [x x y y]
    (cond (nil? y) false
          (nil? x) true
          :else (recur (:next x) (:next y)))))

(defn tail [x y z]
  (if (shorter? y x)
    (tail (tail (:next x) y z) (tail (:next y) z x) (tail (:next z) x y))
    z))

(defn list-length [x] (loop [x x n 0] (if x (recur (:next x) (inc n)) n)))

(defn run [] (list-length (tail (make-list 15) (make-list 10) (make-list 6))))
(def expected 10)
