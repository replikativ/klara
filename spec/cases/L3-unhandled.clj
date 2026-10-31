;; rules: L3.effect.unhandled L3.effect.default
;; expect-rule: :L3.effect.unhandled
(ns e4 (:require [klara.effect :refer [perform]]))
(perform :nobody/handles 1)
