;; rules: L3.handle.deep
;; expect: [:failed "no"]
(ns e3 (:require [klara.effect :refer [perform handle]]))
(handle {:fail (fn [k msg] [:failed msg])} (do (perform :fail "no") :unreachable))
