;; rules: L4.exec.leave L4.exec.frame-state
;; expect: [11 :left]
(ns k9 (:require [klara.stage :refer [code]] [klara.compiler :as compiler] [klara.effect :refer [perform handle]]))
(defn ask [] (perform :ask))
(def f (compiler/executable (compiler/prepare (code (fn [x] (+ x (ask)))))))
(handle {:ask (fn [k] (k 10))} [(f 1) (:last-path (compiler/explain f))])
