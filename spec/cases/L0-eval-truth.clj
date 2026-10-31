;; rules: L0.eval.truth
;; expect: [2 2 1 1 1]
[(if nil 1 2) (if false 1 2) (if 0 1 2) (if "" 1 2) (if [] 1 2)]
