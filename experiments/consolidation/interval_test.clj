(ns consolidation.interval-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.interval :as b]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [klara.core :as c]
            [klara.fusion.kernel :as k]))

(defn expression [op & xs] (apply c/prim op xs))
(deftest kernel-checks-every-intermediate
  (doseq [t [(c/local 0) (c/quote* 7)
              (expression '+ (c/local 0) (c/quote* 2))
              (expression '* (c/local 0) (c/local 0))
              (expression '+ (c/quote* 1)
                          (expression '* (c/local 0) (expression '+ (c/quote* 2) (expression '* (c/local 0) (c/quote* 3)))) )]]
    (let [proof (b/certify t 10 Long/MAX_VALUE)]
      (is (env/verifies? (:environment proof) (:goal proof) (:proof proof)))
      (is (not (env/verifies? (:environment proof)
                              (e/app* (k/c "BoundSafe") (e/lit-nat 100) (e/lit-nat 0) (:term proof))
                              (:proof proof))))))
  (is (thrown? clojure.lang.ExceptionInfo
        (b/certify (expression '* (c/local 0) (c/local 0) (c/quote* 0)) 4000000000 Long/MAX_VALUE)))
  (is (thrown? clojure.lang.ExceptionInfo
        (b/certify (expression '+ (c/local 0) (c/quote* 1)) Long/MAX_VALUE Long/MAX_VALUE))))
