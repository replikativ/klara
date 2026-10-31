(ns klara.private-optimizer
  (:require [klara.local-optimizer] [klara.compiler]))

;; This is ordinary staged guest code. The controller retains all authority;
;; the policy returns only operations from the fixed checked adapter family.
(defn policy-code [inline-rounds]
  (code
    (fn [request]
      (if (< (count (get request :history)) (esc (lift inline-rounds)))
        {:action :local-call :planner 'klara.local-optimizer/planner}
        {:action :private-accumulator}))))

(def policy (run (policy-code 1)))

(defn prepare [job subject]
  (klara.compiler/prepare-request subject
    {:job job :strategy 'klara.private-optimizer/policy
     :backend :baseline :strategy-steps 4}))
