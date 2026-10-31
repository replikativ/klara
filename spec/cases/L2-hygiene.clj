;; rules: L2.code.build
;; expect: 101
(ns s3 (:require [klara.stage :refer [code esc run]]))
(defn wrap [body] (code (let [x 100] (+ x (esc body)))))
((run (code (fn [x] (esc (wrap (code x)))))) 1)
