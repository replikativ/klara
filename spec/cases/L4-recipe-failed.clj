;; rules: L4.prepare.recipe-failed L4.prepare.reference
;; expect: [:L4.prepare.recipe-failed :L4.prepare.recipe-failed]
(ns k5 (:require [klara.stage :refer [code]] [klara.compiler :as compiler]))
[(:rule (compiler/prepare (code (fn [x] x)) {:recipe (fn [_] 42)}))
 (:rule (compiler/prepare (code (fn [x] x)) {:recipe (fn [_] (throw (ex-info "no" {})))}))]
