;; rules: L4.lower.subset
;; expect: :L4.lower.subset
(ns k6 (:require [klara.stage :refer [code]] [klara.compiler :as compiler]))
(:rule (compiler/prepare (code (fn [x] (println x)))))
