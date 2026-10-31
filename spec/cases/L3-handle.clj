;; rules: L3.perform.op L3.handle.deep L3.cont.value
;; expect: [:result 30]
(ns e1 (:require [klara.effect :refer [perform handle]]))
(handle {:ask (fn [k q] (k (* 10 q))) :return (fn [v] [:result v])}
  (+ (perform :ask 1) (perform :ask 2)))
