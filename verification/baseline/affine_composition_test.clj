(ns baseline.affine-composition-test
  (:require [clojure.test :refer [deftest is]] [baseline.affine-composition :as experiment]))

(deftest staged-inlining-exposes-an-existing-owned-region
  (let [r (experiment/run-example)]
    (is (= :scope (get-in r [:before-inlining :check])))
    (is (= [0 1] (get-in r [:ownership-facts 0 :updates])))
    (is (= :terminal-result-only (get-in r [:ownership-facts 0 :escape-policy])))
    (is (= [3 3] (:retained-result r)))
    (is (not= (:original-code-id r) (:residual-code-id r)))
    (is (pos? (get-in r [:native-entry-stats :hits])))
    (is (zero? (get-in r [:native-entry-stats :fallbacks])))
    (is (= {:original-shares-zero-iteration-result true
            :owned-shares-zero-iteration-result false :equal-values true}
           (:host-identity-counterexample r)))))
