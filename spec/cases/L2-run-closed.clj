;; rules: L2.run.closed
;; expect-rule: :L2.run.closed
(ns s8 (:require [klara.stage :refer [code esc run]]))
(def stash (atom nil))
(code (fn [z] (esc (do (reset! stash (code z)) (code 1)))))
(run @stash)
