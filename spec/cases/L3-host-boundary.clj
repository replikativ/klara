;; rules: L3.effect.host-boundary
;; expect-rule: :L3.effect.host-boundary
(ns e5 (:require [klara.effect :refer [perform handle]]))
(handle {:ask (fn [k] (k 1))} (mapv (fn [x] (perform :ask)) [1 2]))
