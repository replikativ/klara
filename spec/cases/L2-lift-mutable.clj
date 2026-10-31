;; rules: L2.lift.mutable
;; expect-rule: :L2.lift.mutable
(ns s9 (:require [klara.stage :refer [lift]]))
(lift [1 (atom 2)])
