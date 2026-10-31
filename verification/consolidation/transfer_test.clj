(ns consolidation.transfer-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.transfer :as transfer] [consolidation.transfer-examples :as examples]
            [ansatz.core :as a] [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [klara.fusion.kernel :as k] [klara.compile.loop :as loop]
            [klara.compile.staged :as staged] [klara.defs :as d] [klara.world :as w]))

(deftest universal-transfer-theorems-check-and-have-no-self-reference
  (doseq [name transfer/theorem-names :let [en @transfer/proof-state d (env/lookup en (nm/from-string name))]]
    (is (env/verifies? en (env/ci-type d) (env/ci-value d)))
    (is (not (contains? (k/constants-of (env/ci-value d)) name)))))

(deftest any-finite-arity-uses-instantiation-not-per-program-tactics
  (force transfer/proof-state)
  (let [before @a/ansatz-env]
    (doseq [arity [0 1 2 3 8 24]
            :let [destinations (mapv #(symbol (str "p" %)) (range arity))
                  arguments (mapv #(hash-map :op :local :name %) (reverse destinations))
                  plan (loop/transfer destinations arguments)
                  receipt (transfer/certify destinations arguments plan)]]
      (is (transfer/verify? destinations arguments plan receipt))
      (is (= arity (get-in receipt [:shape :arity]))))
    (is (identical? before @a/ansatz-env))))

(deftest changed-arguments-temporaries-and-commits-are-rejected
  (let [destinations ['a 'b] arguments [{:op :local :name 'b} {:op :quote :datum 1}]
        plan (loop/transfer destinations arguments) receipt (transfer/certify destinations arguments plan)]
    (doseq [bad [(update plan :evaluations #(vec (reverse %)))
                 (update plan :evaluations pop)
                 (assoc-in plan [:evaluations 0 :expression] {:op :local :name 'a})
                 (assoc-in plan [:evaluations 1 :expression :datum] 1N)
                 (assoc-in plan [:evaluations 1 :temporary] 0)
                 (update plan :commits #(vec (reverse %)))
                 (assoc-in plan [:commits 1 :temporary] 0)
                 (assoc-in plan [:commits 1 :destination] 'a)]]
      (is (thrown? clojure.lang.ExceptionInfo (loop/check-transfer! destinations arguments bad)))
      (is (not (transfer/verify? destinations arguments bad receipt))))
    (doseq [bad [(assoc receipt :goal (:proof receipt))
                 (assoc receipt :proof (:goal receipt))
                 (assoc receipt :proof-sha256 "wrong")
                 (assoc receipt :model-id "unrelated-model")
                 (assoc-in receipt [:shape :plan-id] "stale")]]
      (is (not (transfer/verify? destinations arguments plan bad))))))

(deftest actual-scalar-emission-uses-the-checked-plans
  (doseq [example examples/examples
          :let [result (examples/run-example example)]]
    (is (= (:expected example) (:values result)))
    (is (>= (count (:transfer-evidence result)) 2)))
  (let [source (d/eval-form w/empty-root '(code (fn [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s i)) s)))))
        build loop/transfer]
    ;; A broken proposer must not emit a different RHS despite having the
    ;; right temporary count. This exercises the real emission admission seam.
    (with-redefs [loop/transfer (fn [destinations arguments]
                                 (assoc-in (build destinations arguments) [:evaluations 0 :expression]
                                           {:op :quote :datum 99 :type :long}))]
      (is (thrown? clojure.lang.ExceptionInfo (staged/prepare w/empty-root source))))))
