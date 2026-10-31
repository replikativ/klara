(ns klara.compile.compose-test
  (:require [clojure.test :refer [deftest is]] [klara.compile.view :as view]
            [klara.compile.support :refer [source-code]] [klara.code :as code]
            [klara.eval :as ev] [klara.world :as world] [klara.repl :as repl]
            [klara.compile.staged]))

(deftest fresh-ordered-bindings-do-not-capture-original-scope
  (let [{:keys [nodes]} (view/inspect (source-code '(fn [x] x)))
        root (first nodes) body (second nodes)
        composed (view/compose (:at body) (source-code '(fn [x y] (+ x y)))
                               [(source-code 1) (:code body)])
        result (view/rebuild (:at root) [composed])]
    (is (code/closed? result))
    ;; The second argument refers to the original x, not the fresh x=1.
    (is (= 6 ((ev/run (code/s->core (code/code-term result))) 5)))
    (is (= :let (:op (code/code-term composed))))))

(deftest rejects-foreign-scope-and-invalid-templates
  (let [a (view/inspect (source-code '(fn [x] x))) b (view/inspect (source-code '(fn [y] y)))
        cursor (:at (second (:nodes a))) foreign (:code (second (:nodes b)))]
    (doseq [[template args] [[(source-code '(fn [x] x)) [foreign]]
                            [foreign [(source-code 1)]]
                            [(source-code '(fn [x] x)) []]
                            [(source-code '(fn [& xs] xs)) [(source-code 1)]]
                            [(source-code 0) []]]]
      (is (thrown? clojure.lang.ExceptionInfo (view/compose cursor template args))))))

(deftest unused-and-repeated-arguments-still-evaluate-once-in-order
  (let [s (repl/session)
        setup (repl/eval-response s "(ns bindtest) (def log (clojure.core/atom [])) (defn first-value [] (clojure.core/swap! log conj :first) 10) (defn second-value [] (clojure.core/swap! log conj :second) 20) (def template (code (fn [a b] [a a]))) (def a (code (first-value))) (def b (code (second-value))) (def inspected (perform :stage/inspect (code 0))) (def result (perform :stage/compose (get (nth (get inspected :nodes) 0) :at) template [a b]))")]
    (is (empty? (:errors setup)))
    (is (= "[]" (repl/eval-string s "(clojure.core/deref log)")) "construction executes no arguments")
    (is (= "[10 10]" (repl/eval-string s "(run result)")))
    (is (= "[:first :second]" (repl/eval-string s "(clojure.core/deref log)")))))

(deftest failures-are-not-dropped-or-moved
  (let [cursor (:at (first (:nodes (view/inspect (source-code 0)))))
        template (source-code '(fn [a b] 99))
        division (source-code '(/ 1 0)) index (source-code '(nth [] 0))
        result (view/compose cursor template [division index])]
    (is (thrown? ArithmeticException (ev/run (code/s->core (code/code-term result)))))))

(deftest whole-result-and-arguments-share-the-original-allowance
  (let [v (view/inspect (source-code 0) {:work 32}) cursor (:at (first (:nodes v))) template (source-code '(fn [x] x))]
    (is (= :budget-exhausted
           (try (dotimes [_ 100] (view/compose cursor template [(source-code 1)])) nil
                (catch clojure.lang.ExceptionInfo e (:reason (ex-data e))))))))

(deftest guest-postprocessor-uses-the-existing-prepare-and-install-path
  (let [s (repl/session {:source-roots ["examples/compat"]})
        r (repl/eval-response s "(require '[klara.residual]) (require '[klara.compiler]) (ns post) (def source (code (fn [x] (* x x)))) (def result (klara.residual/postprocess source (code (fn [x] (+ x 1))))) (def kernel (run result)) (klara.compiler/prepare-code result) (kernel 5)")]
    (is (empty? (:errors r)))
    (is (.endsWith ^String (:output r) "26"))
    (is (= "26" (repl/eval-string s "(kernel 5)")))))
