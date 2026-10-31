;; rules: L2.stage.level
;; expect-rule: :L2.stage.level
(ns s6 (:require [klara.stage :refer [code esc]]))
(code (fn [y] (esc y)))
