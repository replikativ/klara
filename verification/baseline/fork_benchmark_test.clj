(ns baseline.fork-benchmark-test
  (:require [clojure.test :refer [deftest is]] [baseline.fork-benchmark :as benchmark]
            [klara.compile.budget :as budget] [klara.defs :as defs] [klara.world :as world]))

(deftest host-memory-and-effects-reject-before-replay
  (let [w (world/make-world) touched (atom 0)
        probe (reify clojure.lang.Counted (count [_] (swap! touched inc) 1))]
    (defs/define! w '(def f (fn [x] (count x))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (benchmark/eligible! (budget/budget) (world/snapshot w) 'f [probe])))
    (is (zero? @touched))
    (defs/define! w '(def mutable (clojure.core/atom 0)))
    (defs/define! w '(def f (fn [x] (clojure.core/swap! mutable inc))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (benchmark/eligible! (budget/budget) (world/snapshot w) 'f [1])))
    (is (= 0 @(:value (world/entry* (world/snapshot w) 'mutable))))))

(deftest nonterminating-reference-exhausts-before-candidate-execution
  (let [w (world/make-world)]
    (defs/define! w '(def f (fn [x] (loop [] (recur)))))
    (is (= :budget-exhausted
           (try (benchmark/eligible! (budget/budget) (world/snapshot w) 'f [1]) nil
                (catch clojure.lang.ExceptionInfo e (:reason (ex-data e))))))))
