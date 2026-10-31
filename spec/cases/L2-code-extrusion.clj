;; rules: L2.code.extrusion
;; expect-rule: :L2.code.extrusion
(ns s7 (:require [klara.stage :refer [code esc]]))
(def stash (atom nil))
(code (fn [z] (esc (do (reset! stash (code z)) (code 1)))))
(code (fn [w] (esc @stash)))
