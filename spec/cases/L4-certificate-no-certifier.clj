;; rules: L4.check.certificate
;; expect: :L4.check.certificate
;; Without a registered certifier (the formal module is not loaded), a
;; certificate is never trusted: the candidate is rejected.
(ns k12 (:require [klara.stage :refer [code]] [klara.compiler :as compiler]))
(:rule (compiler/prepare (code (fn [x] (* x 1)))
                         {:recipe (fn [_] (code (fn [x] x)))
                          :certificate {:kind :ansatz :proof '[(rfl)]}}))
