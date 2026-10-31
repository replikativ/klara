(ns interpreter.activation-checks
  (:require [clojure.test :refer [deftest is]] [interpreter.activation :as a]
            [interpreter.bridge :as b] [interpreter.bridge-checks :as bridge-checks]
            [interpreter.mutable-checks :as cases]
            [klara.expand :as x] [klara.world :as w] [klara.eval :as ev]))

(deftest every-instruction-pause-reconstructs-a-reachable-t0-state
  (doseq [form cases/programs n [0 3]]
    (bridge-checks/compare-trajectory form n a/prepare 2000))
  (binding [*math-context* (java.math.MathContext. 8)]
    (doseq [n [1N 1.00M -0.0 0.0]]
      (bridge-checks/compare-trajectory '(fn [n] (/ n 3)) n a/prepare 2000))))

(defn finish! [c]
  (while (= :paused (b/advance! c 100000)))
  (b/resume! (b/transfer! c)))

(deftest snapshots-tail-reuse-and-higher-order-calls
  (doseq [form (conj cases/programs
                    '(fn [n] (let [make (fn [a b c d e f g h]
                                         (fn [x] (+ a b c d e f g h x)))]
                               ;; Target captures more locals than this caller:
                               ;; stabilize arguments before tail slot reuse.
                               ((make 1 2 3 4 5 6 7 8) n))))
          :let [term (x/expand-expr form w/empty-root) artifact (a/prepare term)
                expected ((ev/run term) 8)]
          fuel [0 1 3 9 30]]
    (let [c (b/start artifact [8]) _ (b/advance! c fuel) snapshot (b/freeze c)]
      (is (= expected (finish! c) (finish! (b/thaw snapshot))
             (b/resume! (b/transfer! (b/thaw snapshot))))))))

(deftest context-errors-and-entry-guards-use-the-shared-controller
  (let [artifact (a/prepare (x/expand-expr '(fn [] (/ 1M 3M)) w/empty-root))
        c (binding [*math-context* (java.math.MathContext. 3)] (b/start artifact []))]
    (binding [*math-context* (java.math.MathContext. 6)]
      (is (= 0.333M (finish! c)))
      (is (= 0.333333M (finish! (b/start artifact []))))))
  (let [artifact (a/prepare (x/expand-expr '(fn [n] (+ n 1)) w/empty-root))
        c (b/start artifact [Long/MAX_VALUE])]
    (is (thrown? ArithmeticException (finish! c)))
    (is (= :failed (b/status c))))
  (is (thrown? clojure.lang.ExceptionInfo
               (a/prepare (x/expand-expr '(fn [x] (println x)) w/empty-root)))))

(deftest common-invoke-and-result-lease
  (doseq [prepare [b/prepare a/prepare]
          form ['(fn [n] (+ n 1)) '(fn [n] (+)) '(fn [n] (*))
                '(fn [n] (vector)) '(fn [n] ((fn [] n)))
                '(fn [n] (+ n 1 2 3 4 5 6 7))]]
    (let [term (x/expand-expr form w/empty-root) artifact (prepare term)]
      (is (= ((ev/run term) 9) (b/invoke artifact 9)))
      (let [c (b/start artifact [9])]
        (while (= :paused (b/advance! c 10000)))
        (is (= ((ev/run term) 9) (b/result! c)))
        (is (= :returned (b/status c)))
        (is (thrown? clojure.lang.ExceptionInfo (b/result! c)))
        (is (thrown? clojure.lang.ExceptionInfo (b/transfer! c)))))))

(deftest generated-program-results-match-clojure-and-node-execution
  (let [random (java.util.Random. 20261029)]
    (letfn [(expression [depth]
              (if (zero? depth) (long (.nextInt random 20))
                (case (.nextInt random 3)
                  0 (list '+ (expression (dec depth)) (expression (dec depth)))
                  1 (list 'if (list '< (expression (dec depth)) 10)
                          (expression (dec depth)) (expression (dec depth)))
                  2 (list 'let ['v (expression (dec depth))]
                          (list '+ 'v (expression (dec depth)))))))]
      (dotimes [_ 60]
        (let [form (list 'fn '[n] (list '+ 'n (expression 3)))
              term (x/expand-expr form w/empty-root) expected ((eval form) 4)]
          (is (= expected (b/invoke (b/prepare term) 4) (b/invoke (a/prepare term) 4))))))))
