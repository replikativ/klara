;; rules: L0.eval.order L0.value.data
;; expect: [1 2 3]
(def log (atom []))
(defn note [x] (swap! log conj x) x)
(note (+ (note 1) (note 2)))
@log
