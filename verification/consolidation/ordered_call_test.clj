(ns consolidation.ordered-call-test
  (:require [clojure.test :refer [deftest is]] [ansatz.core :as a]
            [consolidation.ordered-call :as model]
            [klara.compile.core :as compiler] [klara.compile.local-calls :as local]
            [klara.compile.core-test :refer [setup]] [klara.eval :as ev]
            [klara.world :as world] [klara.defs :as defs] [klara.stage :as stage]))

(deftest stateful-ordering-and-observation-composition-are-kernel-checked
  (let [before @a/ansatz-env receipts (model/verify-theorems!)]
    (is (identical? before @a/ansatz-env))
    (is (= 4 (count receipts)))
    (doseq [r receipts]
      (is (:kernel-accepted r))
      (is (false? (:self-reference r))))))

(deftest actual-recipe-keeps-argument-prefix-and-failure-state
  (doseq [fail-at [nil 1 2]]
    (let [source '(fn [probe] (let [pick (fn [a b] [a a])]
                               (pick (count probe) (count probe))))
          w (setup source) _ (local/bootstrap! w)
          f (defs/lookup (world/snapshot w) 'f) cache (stage/make-cache)
          exe (compiler/compile-def w 'f {:mode :baseline :local-call-planner local/planner-symbol})
          trace (atom [])
          probe (reify clojure.lang.Counted
                  (count [_] (swap! trace conj :argument)
                    (when (= fail-at (count @trace)) (throw (ArithmeticException. "probe failure")))
                    (count @trace)))
          observe (fn [cache]
                    (reset! trace [])
                    [(try [:value (stage/with-cache cache (ev/call-value f [probe]))]
                          (catch Throwable e [:error (class e) (.getMessage e)])) @trace])]
      (stage/install! cache exe)
      (let [expected (observe (stage/make-cache)) actual (observe cache)]
        (is (= expected actual))
        (is (= (if (= fail-at 1) 1 2) (count (second actual))))))))
