(ns consolidation.private-state-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [consolidation.private-state :as p]
            [klara.compile.infer-affine :as ia]
            [klara.compile.staged :as staged]
            [klara.infer-affine-test :as base]
            [klara.stage :as stage]
            [klara.world :as w]
            [klara.fusion.kernel :as k]))

(deftest kernel-checks-analysis-and-simulation
  (let [en (:environment @p/proof-state)]
    (doseq [plan [:done [:alias :done] [:bump [:alias :done]]
                  [:check false [:bump :done]]
                  [:branch true [:alias :done] [:bump :done]]]]
      (let [checked (p/check-plan plan)]
        (is (= :accepted (:status checked)))
        (is (env/verifies? en (:goal checked) (:proof checked)))
        (is (env/verifies? en (p/simulation-goal plan) (:simulation checked)))))
    (doseq [plan [[:retain :done] [:alias [:retain :done]]
                  [:branch true :done [:retain :done]]
                  [:branch false [:retain :done] :done]]]
      (is (= :declined (:status (p/check-plan plan))))
      ;; A forged done proof cannot establish the omitted retention premise.
      (is (not (env/verifies? en (e/app (k/c "PrivateSafe") (p/elaborate-plan plan))
                             (k/c "PrivateSafe.done")))))
    (let [a (p/check-plan [:alias :done])]
      (is (not (env/verifies? en (p/simulation-goal [:retain [:bump :done]]) (:simulation a)))))))

(deftest bounded-model-values-errors-and-outside-frame
  (doseq [plan [:done [:alias [:bump :done]] [:bump [:check false :done]]
                [:check false [:bump :done]]
                [:branch false [:bump :done] [:alias :done]]]
          x (range 4) cap (range 4)]
    (is (= {:answer (p/run-source plan x [17] [41 42] cap) :released true}
           (p/run-target plan x [17] 0 [41 42] cap))))
  (let [unsafe [:retain [:bump :done]]]
    (is (= [0] (:history (p/run-source unsafe 0 [] [41] 10))))
    (is (= [1] (get-in (p/run-target unsafe 0 [] 0 [41] 10) [:answer :history])))
    (is (not= (p/run-source unsafe 0 [] [41] 10)
              (:answer (p/run-target unsafe 0 [] 0 [41] 10))))))

(deftest singleton-loop-conforms-to-the-model
  ;; This is a tested extraction/correspondence bridge, not part of the kernel
  ;; theorem. Exercise actual Long boundaries as well as ordinary iterations.
  (doseq [seed [0 2 (dec Long/MAX_VALUE) Long/MAX_VALUE]]
    (let [form (list 'fn '[n]
                     (list 'loop ['i 0 'acc [seed]]
                           '(let [a acc]
                              (if (< i n) (recur (inc i) (assoc a 0 (inc (nth a 0)))) a))))
          src (base/source form) inferred (ia/infer (base/term src))
          cache (stage/make-cache) candidate (ia/prepare w/empty-root src)]
      (staged/install! cache w/empty-root candidate)
      (doseq [n [0 1 2 5]]
        (let [plan (nth (iterate #(vector :bump %) :done) n)
              model (p/run-source plan seed [] [41] Long/MAX_VALUE)
              project (fn [result]
                        (if (= :value (first result)) {:value (first (second result))}
                            {:error (if (= ArithmeticException (second result))
                                      :overflow (second result))}))
              expected (select-keys model [:value :error])]
          (is (= :accepted (:status (p/check-plan plan))))
          (is (= expected (project (base/observe #(base/call src [n])))))
          (is (= expected (project (base/observe #(ia/execute-owned inferred [n])))))
          (is (= expected (project (stage/with-cache cache (base/observe #(base/call src [n])))))))))))
