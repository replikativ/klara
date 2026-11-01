(ns klara.showcase-test
  "The showcase programs (design/PLAN.md#showcase-programs) run as tests."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(defn- run [path]
  (k/load-file (k/session {:roots ["lib" "."] :out (java.io.StringWriter.)}) path))

(deftest interpreter-to-compiler   ; L4.jit.context L4.jit.attach L4.jit.function L4.check.speculate-value
  (let [r (run "showcases/interpreter_to_compiler.clj")]
    (testing "the user's specializer is checked and installed"
      (is (= [:ready :definitional 1] [(:status r) (:evidence r) (:speculations r)])))
    (testing "compiled and interpreted agree; another expression falls back to the interpreter"
      (is (:same-result r))
      (is (= 42 (:other-expression r))))
    (testing "it pays"
      (is (< 3 (:speedup r))))
    (testing "without the guard the generated code does not mean the interpreter"
      (is (= :rejected (:unguarded r))))))
