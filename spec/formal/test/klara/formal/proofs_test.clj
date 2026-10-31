(ns klara.formal.proofs-test
  "Loading klara.formal.props kernel-checks every definition and theorem of
  the formal semantics; this test fails if any of them did not check."
  (:require [ansatz.core :as a]
            [clojure.test :refer [deftest is]]
            [klara.formal.props]))

(def headline
  '[step-det preservation progress safety run-quote ws-subst ws-pinTm wsb-WS])

(deftest kernel-checked
  (doseq [n headline]
    (is (some? (.lookup ^ansatz.kernel.Env (a/env) (ansatz.kernel.name/from-string (str n))))
        (str n " is in the checked environment"))))
