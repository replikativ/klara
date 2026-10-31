;; rules: L4.exec.deopt
;; expect: [11 :reference]
(ns k9 (:require [klara.stage :refer [code]] [klara.compiler :as compiler] [klara.effect :refer [perform handle]]))
(defn ask [] (perform :ask))
(def f (compiler/executable (compiler/prepare (code (fn [x] (+ x (ask)))))))
(handle {:ask (fn [k] (k 10))} [(f 1) (:last-path (compiler/explain f))])
