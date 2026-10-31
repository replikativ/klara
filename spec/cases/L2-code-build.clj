;; rules: L2.code.build L2.code.value L2.esc.splice L2.run.context
;; expect: [25 true]
(ns s1 (:require [klara.stage :refer [code esc run code?]]))
(defn power-gen [n x] (if (= n 0) (code 1) (code (* (esc x) (esc (power-gen (dec n) x))))))
(def c (code (fn [x] (esc (power-gen 2 (code x))))))
[((run c) 5) (code? c)]
