;; rules: L4.exec.leave L4.lower.calls
;; expect: [101 101]
(ns k-lambda-effect (:require [klara.compiler :as compiler] [klara.effect :refer [perform handle]]))
;; a closure created by compiled code performs (through a callee) under a
;; handler installed by interpreted code: it runs in the caller's machine,
;; where the handler is, as the interpreter's closure does
(defn ask [] (perform :ask))
(defn mk [] (fn [x] (+ x (ask))))
(def interpreted (handle {:ask (fn [k] (k 100))} ((mk) 1)))
(compiler/optimize! 'k-lambda-effect/mk)
[interpreted (handle {:ask (fn [k] (k 100))} ((mk) 1))]
