;; rules: L0.eval.call L0.value.fn L0.term.free
;; expect: [:none [:one 1] [:many 1 (2 3)] 3]
(defn f ([] :none) ([x] [:one x]) ([x & more] [:many x more]))
[(f) (f 1) (f 1 2 3) ((fn [& xs] (count xs)) 1 2 3)]
