(ns consolidation.source-model-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.source-model :as model]
            [consolidation.helper-bridge :as h]
            [klara.infer-affine-test :as base]
            [klara.fusion.kernel :as k]))

(def variants
  ['(fn [n] (loop [i 0 acc [0]]
              (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
   '(fn [n] (loop [i 0 acc [0]]
              (let [a acc b a]
                (if (< i n) (recur (inc i) (assoc b 0 (inc (nth a 0)))) b))))
   '(fn [n] (let [step (fn [a] (let [b a] (assoc b 0 (inc (nth b 0)))))]
              (loop [i 0 acc [0]]
                (let [a acc] (if (< i n) (recur (inc i) (step a)) a)))))])

(deftest original-aliases-and-calls-remain-in-the-model
  (let [models (mapv #(model/extract (base/term (base/source %)) {}) variants)]
    (is (= 3 (count (set (map (comp k/expr-hash :step) models)))))
    (doseq [m models]
      (let [w (h/witness-term (:step m) (:source-id m))]
        (is (h/verify-term-witness? (:step m) (:source-id m) w))))
    ;; The original step syntax changes, but each checked equation gives the
    ;; same universal semantic interface used by the private-loop theorem.
    (let [w (h/witness-term (:step (first models)) (:source-id (first models)))]
      (is (not (h/verify-term-witness? (:step (second models)) (:source-id (second models)) w))))))

(deftest wrong-step-is-rejected-by-semantics-after-structural-extraction
  (let [form '(fn [n] (let [step (fn [a] (assoc a 0 (inc (inc (nth a 0)))))]
                        (loop [i 0 acc [0]]
                          (if (< i n) (recur (inc i) (step acc)) acc))))
        m (model/extract (base/term (base/source form)) {})]
    (is (= :helper-proof
           (try (h/witness-term (:step m) (:source-id m)) :accepted
                (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))))

(deftest a-valid-callee-proof-does-not-license-a-wrong-call-site
  (let [callee '(fn [a] (assoc a 0 (inc (nth a 0))))
        _ (is (h/verify-witness? (base/term (base/source callee))
                                 (h/witness (base/term (base/source callee)))))
        form '(fn [n] (let [step (fn [a] (assoc a 0 (inc (nth a 0))))]
                        (loop [i 0 acc [0]]
                          (if (< i n) (recur (inc i) (step (vector 0))) acc))))
        src (base/source form) m (model/extract (base/term src) {})]
    (is (= [1] (base/call src [2])))
    (is (= :helper-proof
           (try (h/witness-term (:step m) (:source-id m)) :accepted
                (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))))
