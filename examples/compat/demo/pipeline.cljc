(ns demo.pipeline (:require [demo.polynomial :as poly]))

;; Reference evaluation is imported from another guest namespace.
(defn score [x] (poly/evaluate poly/model x))

(defn emit-polynomial [coefficients x]
  (if (empty? coefficients) (code 0)
    (code (+ (esc (lift (first coefficients)))
             (* (esc x) (esc (emit-polynomial (rest coefficients) x)))))))

(defn make-kernel [coefficients]
  (code (fn [x] (esc (emit-polynomial coefficients (code x))))))

;; A world-managed syntax extension; emitted global references are explicit.
(defsyntax polynomial [[coefficients :expr]]
  (list 'demo.pipeline/make-kernel coefficients))

(def kernel-code (polynomial poly/model))
(def kernel (run kernel-code))

(defn refine []
  (let [candidate (fork [job (perform :stage/prepare kernel-code)] (adopt! job))]
    (perform :stage/install candidate)))
