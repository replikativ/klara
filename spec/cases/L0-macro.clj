;; rules: L0.surface.special
;; expect: [:ran nil]
(defmacro unless [c & body] `(if ~c nil (do ~@body)))
[(unless false :ran) (unless true :ran)]
