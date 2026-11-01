(ns awfy.sieve
  "Are We Fast Yet? Sieve: a boolean array, mutated in place.")

(defn sieve [size]
  (let [^booleans flags (boolean-array size true)]
    (loop [i 2 cnt 0]
      (if (<= i size)
        (if (aget flags (dec i))
          (do (loop [k (+ i i)]
                (when (<= k size) (aset flags (dec k) false) (recur (+ k i))))
              (recur (inc i) (inc cnt)))
          (recur (inc i) cnt))
        cnt))))

(defn run [] (sieve 5000))
(def expected 669)
