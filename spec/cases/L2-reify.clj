;; rules: L2.reify.fn L2.reify.preserves L2.reify.host L2.print.form
;; expect: [11 12 2 fn]
(ns s12 (:require [klara.stage :refer [run reify form]] [klara.world :as world]))
(def k 1)
(defn add-k [x] (+ x k))
(def pinned (world/get (world/current) 's12/add-k))
(def k 2)
[((run (reify pinned)) 10) ((run (reify add-k)) 10) ((run (reify inc)) 1) (first (form (reify pinned)))]
