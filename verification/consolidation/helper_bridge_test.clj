(ns consolidation.helper-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.env :as env]
            [consolidation.helper-bridge :as h]
            [klara.infer-affine-test :as base]))

(def helpers
  ['(fn [a] (assoc a 0 (inc (nth a 0))))
   '(fn [a] (let [b a] (assoc b 0 (inc (nth b 0)))))
   '(fn [a] (let [b a c b] (assoc c 0 (inc (nth a 0)))))])

(deftest original-helper-bodies-prove-their-contract
  (doseq [form helpers]
    (let [source (base/term (base/source form)) w (h/witness source)]
      (is (h/verify-witness? source w))
      (is (env/verifies? @h/proof-state (h/private-goal (:term w)) (:private-proof w)))
      ;; Proofs are about all values/iteration counts, not one measured seed.
      (is (not (h/verify-witness? source (assoc w :proof (:private-proof w))))))))

(deftest retained-or-wrong-steps-have-no-requested-witness
  (doseq [form ['(fn [a] [a]) '(fn [a] a) '(fn [a] (assoc a 0 (inc (inc (nth a 0)))))
                '(fn [a] (let [b (vector 0)] (assoc b 0 (inc (nth b 0)))))] ]
    (is (= :helper-proof
           (try (h/witness (base/term (base/source form))) :accepted
                (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex)))))))
  (let [source (base/term (base/source (first helpers))) w (h/witness source)
        other (base/term (base/source '(fn [a] [a])))]
    (is (not (h/verify-witness? other w)))))

(deftest profiling-coincidence-does-not-establish-a-summary
  (let [correct (base/source (first helpers))
        wrong (base/source '(fn [a] (let [b (vector 0)] (assoc b 0 (inc (nth b 0))))))]
    (is (= (base/call correct [[0]]) (base/call wrong [[0]])))
    (is (not= (base/call correct [[7]]) (base/call wrong [[7]])))
    (is (thrown? clojure.lang.ExceptionInfo (h/witness (base/term wrong))))))

(deftest semantic-contracts-distinguish-scalar-and-vector-results
  (let [source (base/term (base/source '(fn [a] (let [b a] (inc (nth b 0))))))
        w (h/witness source :scalar-step)]
    (is (h/verify-witness? source :scalar-step w))
    (is (not (h/verify-witness? source :vector-step w)))
    (is (thrown? clojure.lang.ExceptionInfo (h/witness source :vector-step)))))
