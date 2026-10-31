;; rules: L1.module.require L1.module.ns L1.module.load
;; expect: [true true]
(ns c5 (:require [klara.compiler :as compiler :refer [as-is]]))
[(fn? compiler/prepare) (= as-is compiler/as-is)]
