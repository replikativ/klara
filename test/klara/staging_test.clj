(ns klara.staging-test
  "Staged code values (S4): code/esc/run/lift, hygiene, the dynamic
  scope-extrusion check, let-insertion (genlet, genletrec)."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.code :as code]
            [klara.repl :as repl]))

(defn- session-of [& defs]
  (let [s (repl/session)]
    (doseq [d defs] (repl/eval-string s d))
    s))

(defn- ev [s form] (repl/eval-string s form))

(def power
  "(def power (fn [n x] (if (zero? n) (code 1) (code (* (esc x) (esc (power (dec n) x)))))))")

(deftest brackets-escapes-run
  (let [s (session-of power)]
    (is (= "(code (+ 1 2))" (ev s "(code (+ 1 2))")))
    (is (= "3" (ev s "(run (code (+ 1 2)))")))
    (is (= "(code (fn [y_1] (* y_1 (* y_1 (* y_1 1)))))"
           (ev s "(code (fn [y] (esc (power 3 (code y)))))")))
    (is (= "8" (ev s "((run (code (fn [y] (esc (power 3 (code y)))))) 2)")))
    (testing "generated code resolves world definitions under the run basis"
      (is (= "#'sq" (ev s "(def sq (fn [x] (* x x)))")))
      (is (= "(code (sq 3))" (ev s "(code (sq 3))")))
      (is (= "9" (ev s "(run (code (sq 3)))"))))
    (testing "levels > 1"
      (is (= "(code (code (+ 1 (esc 2))))" (ev s "(code (code (+ 1 (esc (esc (code 2))))))")))
      (is (= "3" (ev s "(run (run (code (code (+ 1 2)))))"))))
    (testing "esc outside code is an expansion error; esc of a non-code is a stage error"
      (is (= "!! expand: esc outside code" (ev s "(esc 1)")))
      (is (= "!! stage: esc expects a code value, got 3" (ev s "(code (esc 3))")))
      (is (= "!! stage: run expects a code value, got 3" (ev s "(run 3)"))))))

(deftest hygiene
  (let [s (session-of)]
    (testing "binders in generated code are fresh: a spliced variable is never captured"
      (is (= "(code (fn [x_1] (fn [x_2] x_1)))"
             (ev s "(let [mk (fn [body] (code (fn [x] (esc body))))] (code (fn [x] (esc (mk (code x))))))")))
      (is (= "1" (ev s "(((run (let [mk (fn [body] (code (fn [x] (esc body))))] (code (fn [x] (esc (mk (code x))))))) 1) 2)"))))
    (testing "printed names do not depend on earlier generation"
      (is (= (ev s "(code (fn [a] a))") (ev s "(code (fn [a] a))") "(code (fn [a_1] a_1))")))
    (testing "a binder of generated code seen from level 0 is its code"
      (is (= "(code (fn [z_1] (+ z_1 z_1)))" (ev s "(code (fn [z] (+ z (esc z))))"))))))

(deftest scope-extrusion
  (let [s (session-of)]
    (testing "the classic counterexample: open code stored in a mutable cell, spliced later"
      (is (= (str "!! scope-extrusion: code mentions x, whose binder is not in scope where it is spliced"
                  " (a variable escaped the code that binds it)")
             (ev s (str "(let [r (atom nil)]"
                        "  (code (fn [x] (esc (do (reset! r (code x)) (code x)))))"
                        "  (code (fn [y] (esc @r))))")))))
    (testing "... or run later"
      (is (re-find #"^!! scope-extrusion: code mentions x, whose binder is not in scope where the code is run"
                   (ev s "(let [r (atom nil)] (code (fn [x] (esc (do (reset! r (code x)) (code x))))) (run @r))"))))
    (testing "open code that stays inside its binder's extent is fine, through helper fns"
      (is (= "(code (fn [x_1] (fn [y_2] (+ y_2 x_1))))"
             (ev s "(let [wrap (fn [c] (code (fn [y] (+ y (esc c)))))] (code (fn [x] (esc (wrap (code x))))))"))))
    (testing "running open code inside its binder is still refused: run needs closed code"
      (is (re-find #"^!! scope-extrusion" (ev s "(code (fn [x] (esc (do (run (code x)) (code 1)))))"))))
    (testing "code built in a callback of a host function sees the enclosing binders"
      (is (= "(code (fn [x_1] (+ (+ (+ 0 (* x_1 1)) (* x_1 2)) (* x_1 3))))"
             (ev s "(code (fn [x] (esc (reduce (fn [acc i] (code (+ (esc acc) (* x (esc (lift i)))))) (code 0) [1 2 3]))))"))))))

(deftest lift-and-persistence
  (let [s (session-of)]
    (is (= "(code [1 :a \"s\" {:b 2}])" (ev s "(lift [1 :a \"s\" {:b 2}])")))
    (is (= "(code (quote sym))" (ev s "(lift (quote sym))")))
    (is (= "(code (+ 5 1))" (ev s "(let [n 5] (code (+ n 1)))")) "implicit lift of a present value")
    (is (= "(code ((fn [z_1] (* z_1 2)) 3))"
           (ev s "(let [k 2 f (fn [z] (* z k))] (code (f 3)))"))
        "a closure persists as its code over its lifted captures")
    (is (= "6" (ev s "(run (let [k 2 f (fn [z] (* z k))] (code (f 3))))")))
    (testing "refusals"
      (is (= "!! lift: cannot lift a value holding a resource (Atom); only data and functions over data persist into code"
             (ev s "(lift (atom 1))")))
      (is (re-find #"^!! lift: cannot lift a value holding a resource \(Atom\)"
                   (ev s "(let [a (atom 0) f (fn [] (swap! a inc))] (lift f))"))
          "a closure over a resource")
      (is (re-find #"^!! lift: cannot lift a value holding a resource \(a handler instance\)"
                   (ev s "(handle [h {:op (fn [k] (k 1))}] (lift h))")))
      (is (= "!! lift: cannot lift a code value (splice it with esc instead)" (ev s "(lift (code 1))")))
      (is (= "!! stage: a code value is used inside code without esc"
             (ev s "(let [c (code 1)] (code (+ 1 c)))"))))))

(deftest let-insertion
  ;; expected placements follow ber-metaocaml-153/test/genlet.ml
  (let [s (session-of)]
    (is (= "(code (+ 1 2))" (ev s "(code (+ 1 (esc (genlet (code 2)))))")) "values are not bound")
    (is (= "(code (let [t_1 (+ 1 2)] (fn [x_2] (+ x_2 t_1))))"
           (ev s "(code (fn [x] (+ x (esc (genlet (code (+ 1 2)))))))"))
        "a closed expression floats out of the fn")
    (is (= "(code (fn [x_1] (+ x_1 x_1)))" (ev s "(code (fn [x] (+ x (esc (genlet (code x))))))")))
    (is (= "(code (fn [x_1] (let [t_2 (+ x_1 1)] (+ x_1 t_2))))"
           (ev s "(code (fn [x] (+ x (esc (genlet (code (+ x 1)))))))"))
        "it stops at the binder of its free variable")
    (is (= "(code (fn [x_1] (let [t_2 (+ x_1 1)] (fn [y_3] (+ (+ x_1 y_3) t_2)))))"
           (ev s "(code (fn [x] (fn [y] (+ (+ x y) (esc (genlet (code (+ x 1))))))))")))
    (is (= "(code (let [t_1 (+ 1 2)] (fn [x_2 y_3] (let [t_4 (+ y_3 t_1)] (+ (+ x_2 y_3) t_4)))))"
           (ev s "(code (fn [x y] (+ (+ x y) (esc (genlet (code (+ y (esc (genlet (code (+ 1 2)))))))))))"))
        "nested genlet")
    (is (= "12" (ev s "((run (code (fn [x y] (+ (+ x y) (esc (genlet (code (+ y (esc (genlet (code (+ 1 2)))))))))))) 1 4)")))
    (is (= "(code (+ 1 2))" (ev s "(genlet (code (+ 1 2)))")) "no locus: unchanged")
    (testing "a dynamic handler may override the stage operation"
      (is (= "(code (fn [x_1] (+ x_1 (+ 1 2))))"
             (ev s "(handle :dynamic {:stage/genlet (fn [c k] (k c))} (code (fn [x] (+ x (esc (genlet (code (+ 1 2))))))))"))))
    (testing "a let-bound variable escaping through a cell is caught"
      (is (re-find #"^!! scope-extrusion: code mentions t"
                   (ev s "(let [r (atom nil)] (code (fn [x] (esc (do (reset! r (genlet (code (+ x 1)))) (code x))))) (run @r))"))))))

(deftest genletrec
  ;; ber-metaocaml-153/test/genletrec.ml: gibonacci and Ackermann
  (let [s (session-of
           (str "(def sfib (fn [n] (with-genletrec [g]"
                "  (letfn [(gen [n] (cond (= n 0) (code (fn [x y] x))"
                "                         (= n 1) (code (fn [x y] y))"
                "                         :else (code (fn [x y] (+ ((esc (g gen (- n 1))) x y)"
                "                                                  ((esc (g gen (- n 2))) x y))))))]"
                "    (code (fn [x y] ((esc (g gen n)) x y)))))))")
           (str "(def sack (fn [m] (with-genletrec [g]"
                "  (letfn [(gen [m] (if (= m 0) (code (fn [n] (+ n 1)))"
                "                     (code (fn [n] (if (= n 0) ((esc (g gen (- m 1))) 1)"
                "                                       ((esc (g gen (- m 1))) ((esc (g gen m)) (- n 1))))))))]"
                "    (g gen m)))))"))]
    (is (= "8" (ev s "((run (sfib 5)) 1 1)")))
    (is (= "(code (letfn [(h_1 [x_4 y_5] (+ (h_2 x_4 y_5) (h_3 x_4 y_5))) (h_2 [x_6 y_7] y_7) (h_3 [x_8 y_9] x_8)] (fn [x_10 y_11] (h_1 x_10 y_11))))"
           (ev s "(sfib 2)")))
    (is (= "100" (ev s "(code-size (sfib 10))")) "linear in n")
    (is (= "(code (letfn [(h_1 [n_4] (if (= n_4 0) (h_2 1) (h_2 (h_1 (- n_4 1))))) (h_2 [n_5] (if (= n_5 0) (h_3 1) (h_3 (h_2 (- n_5 1))))) (h_3 [n_6] (+ n_6 1))] h_1))"
           (ev s "(sack 2)"))
        "Ackermann specialized to m terminates thanks to memoization")
    (is (= "9" (ev s "((run (sack 2)) 3)")))
    (is (= "!! scope-extrusion: genletrec generator used outside its with-genletrec"
           (ev s "(let [r (atom nil)] (with-genletrec [g] (do (reset! r g) (code 1))) (@r (fn [k] (code (fn [] 1))) 1))")))
    (is (= "(code (fn [z_1] (fn h_2 [] z_1)))"
           (ev s "(code (fn [z] (esc (with-genletrec [g] (g (fn [k] (code (fn [] z))) 1)))))"))
        "a binding may mention variables in scope at the locus")
    (is (re-find #"^!! scope-extrusion: code mentions z, whose binder is not in scope at the with-genletrec"
                 (ev s "(with-genletrec [g] (code (fn [z] (esc (g (fn [k] (code (fn [] z))) 1)))))"))
        "... but not variables bound inside it")))

(deftest printing-and-repl
  (let [s (session-of power)]
    (is (= "(fn [y_1] (* y_1 (* y_1 1)))" (ev s ":code (code (fn [y] (esc (power 2 (code y)))))")))
    (is (= "(let [a_1 1 b_2 2] (+ a_1 b_2))" (ev s ":expand (let [a 1 b 2] (+ a b))")))
    (is (= "true" (ev s "(closed? (code (fn [x] x)))")))
    (is (code/code? (code/->code {:op :quote :datum 1})))))
