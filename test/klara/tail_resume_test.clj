(ns klara.tail-resume-test
  "resume-in-place (klara.runtime.machine) shortcuts the rule for clauses
  (fn [k ..] (k e)) inside the reference interpreter. It must change
  nothing observable: every spec case has the same outcome without it."
  (:require [clojure.test :refer [deftest testing]]
            [klara.conformance-test :as conformance]
            [klara.runtime.machine :as m]))

(deftest conformance-without-tail-resume   ; L3.handle.deep L3.budget.steps L3.budget.exhausted L4.profile.record
  (reset! m/tail-resume? false)
  (try (testing "with every effect taking the rule as written"
         (conformance/check-cases))
       (finally (reset! m/tail-resume? true))))
