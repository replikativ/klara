(ns consolidation.scalar-block-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.scalar-block :as block]
            [consolidation.scalar-core-test :as cases]
            [ansatz.core :as a] [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [consolidation.scalar-core :as scalar]
            [klara.fusion.kernel :as k] [klara.core :as c]))

(deftest source-specific-refinements-compose-with-cek-execution
  (let [en @block/proof-state d (env/lookup en (nm/from-string "slot-block-cek"))]
    (is (env/verifies? en (env/ci-type d) (env/ci-value d)))
    (is (not (contains? (k/constants-of (env/ci-value d)) "slot-block-cek"))))
  (doseq [body cases/bodies
          :let [receipt (block/certify body 2)
                emitted (block/emit-long body 2 receipt)]]
    (is (block/verify? body 2 receipt))
    (doseq [args [[0 0] [4 3] [19 7]]]
      (is (= (cases/evaluate body args) (apply (:invoke emitted) args))))))

(deftest per-source-proof-jobs-use-the-captured-model-environment
  (force block/proof-state)
  ;; Model bootstrapping follows existing ansatz REPL modules. Subsequent proof
  ;; jobs must not depend on, or install declarations into, that global session.
  (with-redefs [a/ansatz-env (atom @scalar/proof-state)]
    (let [before @a/ansatz-env
          body (c/prim '+ (c/local 0) (c/quote* 2))
          receipt (block/certify body 1)]
      (is (block/verify? body 1 receipt))
      (is (identical? before @a/ansatz-env)))))

(deftest stale-or-unrelated-certificates-and-invalid-blocks-decline
  (let [body (c/prim '+ (c/local 1) (c/local 0))
        receipt (block/certify body 2)
        wrong-block (assoc-in (:block receipt) [:instructions 2 0] :mul)]
    ;; The changed block is structurally well formed but computes a different
    ;; answer; freshness/ownership checks alone cannot justify its admission.
    (is (some? (block/encode-block wrong-block)))
    (is (thrown? clojure.lang.ExceptionInfo (block/certify body 2 wrong-block)))
    (doseq [bad [(assoc receipt :source-id "stale")
                 (assoc receipt :arity 1)
                 (assoc receipt :block wrong-block)
                 (assoc receipt :proof (:goal receipt))
                 (assoc receipt :proof-sha256 "wrong")
                 (assoc receipt :execution-proof (:execution-goal receipt))]]
      (is (false? (block/verify? body 2 bad)))
      (is (thrown? clojure.lang.ExceptionInfo (block/emit-long body 2 bad))))
    (doseq [bad [(assoc-in (:block receipt) [:instructions 0 2] 99)
                 (assoc-in (:block receipt) [:instructions 0 1] 3)
                 (assoc (:block receipt) :result 99)]]
      (is (thrown? clojure.lang.ExceptionInfo (block/encode-block bad))))))

(deftest emitted-bridge-preserves-overflow-and-declares-its-input-boundary
  (let [body (c/prim '* (c/prim '+ (c/local 0) (c/quote* 1)) (c/quote* 0))
        receipt (block/certify body 1)
        f (:invoke (block/emit-long body 1 receipt))]
    (is (= 0 (f 4)))
    (is (thrown? ArithmeticException (cases/evaluate body [Long/MAX_VALUE])))
    (is (thrown? ArithmeticException (f Long/MAX_VALUE)))
    ;; Folding the final mathematical answer to zero would erase a required
    ;; overflowing intermediate. A well-formed constant block must fail proof.
    (is (thrown? clojure.lang.ExceptionInfo
                 (block/certify body 1 {:arity 1 :instructions [[:literal 1 0]]
                                       :result 1 :next 2})))
    (doseq [v [-1 1N 1.0 (atom 0)]]
      (is (thrown? clojure.lang.ExceptionInfo (f v))))
    (is (thrown? clojure.lang.ExceptionInfo (f)))
    (with-redefs [c/prims (assoc c/prims '+ (fn [& _] :wrong))]
      (is (thrown? clojure.lang.ExceptionInfo (f 4))))))
