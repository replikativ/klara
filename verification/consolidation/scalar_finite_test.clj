(ns consolidation.scalar-finite-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.scalar-finite :as finite]
            [consolidation.scalar-core-test :as scalar-test]
            [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [klara.fusion.kernel :as k] [klara.core :as c]))

(deftest finite-environment-theorems-check-independently
  (doseq [name finite/theorem-names
          :let [en @finite/proof-state d (env/lookup en (nm/from-string name))]]
    (is (env/verifies? en (env/ci-type d) (env/ci-value d)))
    (is (not (contains? (k/constants-of (env/ci-value d)) name)))))

(deftest finite-execution-binds-source-scope-and-interface
  (doseq [body scalar-test/bodies
          :let [receipt (finite/execution-witness body 2)]]
    (is (finite/verify-execution? body 2 receipt))
    (doseq [bad [(assoc receipt :source-id "wrong")
                 (assoc receipt :goal-sha256 "wrong")
                 (assoc receipt :proof-sha256 "wrong")
                 (assoc receipt :proof (:goal receipt))
                 (assoc-in receipt [:scope-witness :arity] 1)
                 (assoc-in receipt [:scope-witness :proof] (:goal receipt))]]
      (is (not (finite/verify-execution? body 2 bad))))
    (is (not (finite/verify-execution? (c/quote* 0) 2 receipt)))
    (is (not (finite/verify-execution? body 3 receipt)))))

(deftest unsupported-syntax-and-escaping-indices-decline
  (doseq [[body arity] [[(c/local 1) 1] [(c/quote* -1) 0]
                       [(c/prim '- (c/quote* 2) (c/quote* 1)) 0]]]
    (is (thrown? Exception (finite/execution-witness body arity)))))
