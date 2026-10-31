(ns demo.polynomial)

(def model #?(:klara [3 2 1] :clj [3 2 1]))

(defn evaluate [coefficients x]
  (if (empty? coefficients) 0
    (+ (first coefficients) (* x (evaluate (rest coefficients) x)))))

(defn scores [inputs]
  (mapv (fn [x] (evaluate model x)) inputs))

(defn summary [inputs]
  (let [values (scores inputs)]
    {:count (count values) :sum (reduce + 0 values) :scores values}))
