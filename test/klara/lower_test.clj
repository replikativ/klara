(ns klara.lower-test
  "Lowering (L4.lower.*) on terms specializers can build but the expander
  never produces."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.lower :as lower]
            [klara.host.api :as k]))

(deftest L4-lower-steps-parallel-binding
  (testing "an inlined function called with locals of its own parameter names binds them in parallel"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (is (= [:ready 2 2]
             (k/eval-string s "(ns lw (:require [klara.stage :refer [code run]] [klara.code :as c] [klara.compiler :as compiler]))
               (defn local [n] (c/make {:op :local :name n}))
               ;; (fn [x y] ((fn [x y] (- x y)) y x)): the inner x is the outer y
               (def candidate
                 (c/make {:op :fn :params '[x y]
                          :body (c/make {:op :app
                                         :fn (c/make {:op :fn :params '[x y]
                                                      :body (c/make {:op :app :fn (c/make {:op :host :name 'klara.core/-})
                                                                     :args [(local 'x) (local 'y)]})})
                                         :args [(local 'y) (local 'x)]})}))
               (def o (compiler/prepare (code (fn [a b] (- b a))) {:recipe (fn [_] candidate)}))
               (def f (compiler/executable o))
               [(:status o) (f 3 5) ((run candidate) 3 5)]"))))))

(deftest L4-lower-direct   ; L4.lower.direct
  (testing "compiled code calls compiled code directly, and generally again once the callee changes"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (is (= [7 10]
             (k/eval-string s "(ns ld (:require [klara.compiler :as compiler]))
               (defn g [x] (* 2 x))
               (defn f [x] (+ (g x) 1))
               (compiler/optimize! 'ld/g)
               (compiler/optimize! 'ld/f)
               (def a (f 3))
               (defn g [x] (* 3 x))
               [a (f 3)]"))))))

(deftest L4-exec-leave-host-boundary
  (testing "a compiled lambda that leaves while host code runs it finishes there, in a nested machine"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (k/eval-string s "(ns lb (:require [klara.compiler :as compiler]))
        (defn h [xs] (reduce + (map (fn [x] (* x x)) xs)))
        (compiler/optimize! 'lb/h)")
      (reset! lower/stress 0.5)
      (try
        (is (= #{328350} (set (k/eval-string s "(vec (for [_ (range 30)] (h (range 100))))"))))
        (finally (reset! lower/stress nil))))))

(deftest L4-lower-hint   ; L4.lower.hint
  (testing "a type hint is a guard: right, it is used; wrong, the interpreter goes on"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (is (= [3 3 "abc" :left]
             (k/eval-string s "(ns lh (:require [klara.compiler :as compiler]))
               (defn n-true [n] (let [^booleans a (boolean-array n true)] (loop [i 0 c 0] (if (< i n) (recur (inc i) (if (aget a i) (inc c) c)) c))))
               (defn wrong [x] (let [^String s (str x)] (let [^longs v s] (str v))))
               (compiler/optimize! 'lh/n-true)
               (compiler/optimize! 'lh/wrong)
               [(n-true 3) (n-true 3) (wrong \"abc\") (:last-path (compiler/explain wrong))]"))))))
