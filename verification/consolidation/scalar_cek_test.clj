(ns consolidation.scalar-cek-test
  (:require [clojure.test :refer [deftest is]] [consolidation.scalar-cek :as cek]
            [consolidation.scalar-core-test :as scalar-test]
            [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [klara.fusion.kernel :as k] [klara.core :as c]))

(deftest kernel-CEK-proofs-check-independently
  (doseq [name cek/theorem-names :let [en @cek/proof-state d (env/lookup en (nm/from-string name))]]
    (is (env/verifies? en (env/ci-type d) (env/ci-value d)))
    (is (not (contains? (k/constants-of (env/ci-value d)) name)))))

(deftest bounded-frame-execution-agrees-with-T0-and-actual-endpoint-proofs
  (let [random (java.util.Random. 3201)]
    (doseq [body scalar-test/bodies]
      (let [receipt (cek/execution-witness body [10 10]) fuel (cek/step-bound body)]
        (is (cek/verify-execution? body [10 10] receipt))
        (is (not (cek/verify-execution? body [10 10] (assoc receipt :proof (:goal receipt)))))
        (dotimes [_ 16]
          (let [args [(long (.nextInt random 11)) (long (.nextInt random 11))]
                result (cek/observe body args Long/MAX_VALUE fuel)]
            (is (= :done (:status result)))
            (is (= [:ok (scalar-test/evaluate body args)] (:answer result)))
            (is (= fuel (:steps result)))))))))

(deftest fuel-exhaustion-is-pending-and-errors-unwind-frames
  (let [body (c/prim '+ (c/local 0) (c/quote* 1)) fuel (cek/step-bound body)]
    (is (= :pending (:status (cek/observe body [3] Long/MAX_VALUE (dec fuel)))))
    (is (= :done (:status (cek/observe body [Long/MAX_VALUE] Long/MAX_VALUE fuel))))
    (is (= [:overflow] (:answer (cek/observe body [Long/MAX_VALUE] Long/MAX_VALUE fuel)))))
  (let [body (c/let1 (c/prim '* (c/local 0) (c/local 0)) (c/prim '+ (c/local 0) (c/quote* 1)))]
    (is (= [:overflow] (:answer (cek/observe body [Long/MAX_VALUE] Long/MAX_VALUE (cek/step-bound body)))))))
