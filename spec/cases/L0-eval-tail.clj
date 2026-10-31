;; rules: L0.eval.tail L0.space.tail L0.term.loop
;; expect: [:done 4999950000]
(defn count-down [n] (if (= n 0) :done (count-down (dec n))))
[(count-down 100000) (loop [i 0 acc 0] (if (< i 100000) (recur (inc i) (+ acc i)) acc))]
