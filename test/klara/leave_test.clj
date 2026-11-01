(ns klara.leave-test
  "Leaving compiled code (L4.exec.leave, L4.exec.frame-state, L4.check.speculate):
  compiled code hands the interpreter a state it would itself have reached,
  and nothing runs twice."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.lower :as lower]
            [klara.host.api :as k]))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(deftest L4-exec-leave-effects
  (testing "a callee's effect leaves compiled code; earlier work is not repeated"
    (let [s (session)]
      (is (= [11 1 :left]
             (k/eval-string s "(ns e1 (:require [klara.compiler :as compiler] [klara.effect :refer [perform handle]]))
               (def counter (atom 0))
               (defn bump [] (swap! counter inc) 1)
               (defn ask [] (perform :ask))
               (defn f [x] (let [a (bump) b (ask)] (+ x a b)))
               (compiler/optimize! 'e1/f)
               (def r (handle {:ask (fn [k] (k 9))} (f 1)))
               [r @counter (:last-path (compiler/explain f))]"))))))

(deftest L4-exec-leave-budget
  (testing "running out of budget inside a compiled loop suspends there; resuming finishes the same loop"
    (let [s (session)]
      (is (= [:exhausted 4999950000 true]
             (k/eval-string s "(ns e2 (:require [klara.compiler :as compiler] [klara.job :as job]))
               (defn sum-to [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc i)) acc)))
               (compiler/optimize! 'e2/sum-to)
               (def full (job/run {:budget {:steps 1000000}} (fn [] (sum-to 100000))))
               (def part (job/run {:budget {:steps 1000}} (fn [] (sum-to 100000))))
               (def rest (job/resume part {:steps 1000000}))
               [(:status part) (:value rest)
                ;; no restart: the two parts together cost about what one run costs
                (< (+ (:steps (:spent part)) (:steps (:spent rest))) (+ (:steps (:spent full)) 10))]"))))))

(deftest L4-check-speculate
  (testing "a speculation compiles its guarded branch and leaves through its reference branch"
    (let [s (session)]
      (is (= [:ready 6 :compiled 3.0 :left :rejected]
             (k/eval-string s "(ns e3 (:require [klara.stage :refer [code esc]] [klara.compiler :as compiler] [klara.jit :as jit]))
               (def reference (code (fn [x] (* x 2))))
               (def o (compiler/prepare reference
                        {:recipe (fn [_] (code (fn [x] (esc (jit/guard (code (int? x)) (code (* x 2)) (code (* x 2)))))))}))
               (def f (compiler/executable o))
               (def a (f 3)) (def pa (:last-path (compiler/explain f)))
               (def b (f 1.5)) (def pb (:last-path (compiler/explain f)))
               ;; the specialized branch must mean the reference too
               (def bad (compiler/prepare reference
                          {:recipe (fn [_] (code (fn [x] (esc (jit/guard (code (int? x)) (code (+ x 1)) (code (* x 2)))))))}))
               [(:status o) a pa b pb (:status bad)]"))))))

(deftest L4-exec-frame-state-callers
  (testing "a leave deep inside compiled callers rebuilds every caller's frame"
    (let [s (session)]
      (reset! lower/stress 1.0)
      (try
        (is (= 6765 (k/eval-string s "(ns e4 (:require [klara.compiler :as compiler]))
                       (defn fib [n] (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
                       (compiler/optimize! 'e4/fib)
                       (fib 20)")))
        (finally (reset! lower/stress nil))))))
