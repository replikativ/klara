(ns consolidation.indexed-binding-test
  (:require [clojure.test :refer [deftest is]] [ansatz.core :as a]
            [consolidation.indexed-binding :as model]))
(deftest lexical-renaming-model-is-kernel-checked
  (let [before @a/ansatz-env receipts (model/verify-theorems!)]
    (is (identical? before @a/ansatz-env))
    (is (= 2 (count receipts)))
    (doseq [r receipts] (is (:kernel-accepted r)) (is (false? (:self-reference r))))))
