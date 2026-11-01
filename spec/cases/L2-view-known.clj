;; rules: L2.view.unfold L2.view.known
;; expect: [:fn true nil 42 true false]
(ns vk (:require [klara.stage :refer [code]] [klara.code :as c] [klara.compiler :as compiler]))
(defn sq [x] (* x x))
(def answer 42)
(def box (atom 1))
(compiler/optimize! 'vk/sq)
[(:op (c/view (c/unfold (code vk/sq))))          ; the definition, also when compiled
 (some? (c/known (code vk/answer)))
 (c/known (code vk/box))                          ; mutable: not known
 (:value (c/view (c/known (code vk/answer))))
 (c/pure-host? (code inc))
 (c/pure-host? (code println))]
