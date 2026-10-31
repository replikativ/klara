;; rules: L2.esc.not-code
;; expect-rule: :L2.esc.not-code
(ns s5 (:require [klara.stage :refer [code esc]]))
(code (+ 1 (esc 2)))
