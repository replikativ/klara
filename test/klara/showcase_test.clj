(ns klara.showcase-test
  "The showcase programs (design/PLAN.md#showcase-programs) run as tests."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(defn- run [path]
  (k/load-file (k/session {:roots ["lib" "."] :out (java.io.StringWriter.)}) path))

(deftest interpreter-to-compiler   ; L4.jit.context L4.jit.attach L4.jit.function L4.check.speculate-value L4.jit.simplify L4.check.delta-data
  (let [r (run "showcases/interpreter_to_compiler.clj")]
    (testing "the user's specializer is checked and installed"
      (is (= [:ready :definitional 1] [(:status r) (:evidence r) (:speculations r)])))
    (testing "compiled and interpreted agree; another expression falls back to the interpreter"
      (is (:same-result r))
      (is (= 42 (:other-expression r))))
    (testing "it pays"
      (is (< 3 (:speedup r))))
    (testing "without the guard the generated code does not mean the interpreter"
      (is (= :rejected (:unguarded r))))
    (testing "a caller that passes a known definition needs no guard: the call is specialized away"
      (is (= :ready (:driver r)))
      (is (every? (set (:driver-premises r)) '[showcases.interpreter-to-compiler/calc
                                               showcases.interpreter-to-compiler/model]))
      (is (:same-specialized r)))))

(deftest speculate-fail-continue  ; L4.check.speculate-assume L4.jit.inline L4.exec.osr L4.exec.mint-safe L2.view.children
  (let [r (run "showcases/speculate_fail_continue.clj")]
    (testing "a loop that performs an effect compiles only by speculating on its cold branch"
      (is (= [:rejected :ready 1] [(:without-speculation r) (:status r) (:speculations r)])))
    (testing "the refund leaves compiled code once; the effect happens once; the result is the interpreter's"
      (is (= [true 1 :left] [(:same-result r) (:reviews r) (:left-at-refund r)])))
    (testing "after the effect the loop runs compiled again"
      (is (pos? (:reentered-compiled-loop r))))
    (testing "inlining made the helper a premise: changing it retires the compiled loop, not in the old world"
      (is (= :interpreted (:after-fee-change-runs r)))
      (is (:old-world-keeps r))
      (is (#{:compiled :left} (:old-world-path r))))))
