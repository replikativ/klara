(ns klara.compile.view-test
  (:require [clojure.test :refer [deftest is]] [klara.compile.support :refer [source-code]] [klara.compile.view :as view]
            [klara.compile.staged] [klara.compile.core :as compiler]
            [klara.core :as core] [klara.code :as code] [klara.eval :as ev]
            [klara.expand :as expand] [klara.world :as world] [klara.defs :as defs]
            [klara.repl :as repl] [klara.stage :as stage]))

(defn id [c] (core/code-id (code/s->core (code/code-term c))))
(defn regenerate [c]
  (let [{:keys [root nodes]} (view/inspect c)]
    (letfn [(visit [i]
              (let [d (nth nodes i)] (view/rebuild (:at d) (mapv visit (:children d)))))]
      (visit root))))

(deftest structural-roundtrip-covers-binders-and-control
  (doseq [form ['(fn [x] (let [y (+ x 1)] (if (< y 0) (- y) (* y y))))
               '(fn [n] (loop [i n a 1 b 2] (if (> i 0) (recur (dec i) b (+ a b)) a)))
               '(fn [n] (letfn [(even [i] (if (= i 0) true (odd (dec i))))
                                (odd [i] (if (= i 0) false (even (dec i))))] (even n)))
               '(fn [f x] (f x)) '(fn [x] {:answer [x nil false "ok"]})]]
    (let [original (source-code form) rebuilt (regenerate original)]
      (is (code/closed? rebuilt))
      (is (= (id original) (id rebuilt))))))

(deftest cursor-enforces-child-scope-and-shape
  (let [a (view/inspect (source-code '(fn [x] x)))
        b (view/inspect (source-code '(fn [y] y)))
        root-a (first (:nodes a)) body-a (second (:nodes a)) body-b (second (:nodes b))]
    (is (thrown? clojure.lang.ExceptionInfo (view/rebuild (:at root-a) [(:code body-b)])))
    (is (thrown? clojure.lang.ExceptionInfo (view/inspect (:code body-a))))
    (is (thrown? clojure.lang.ExceptionInfo (view/rebuild root-a [(:code body-a)])))
    (is (thrown? clojure.lang.ExceptionInfo (view/rebuild (:at root-a) [])))
    (is (= :fn (:op (code/code-term (view/rebuild (:at (assoc root-a :op :quote)) [(:code body-a)])))))
    ;; A closed replacement needs no ambient binder permission. Scope safety
    ;; deliberately does not assert it is equivalent to the original body.
    (let [replacement (code/->code {:op :quote :datum 42})
          c (view/rebuild (:at root-a) [replacement])]
      (is (= 42 ((ev/run (code/s->core (code/code-term c))) 0))))))

(deftest repeated-splices-get-distinct-binder-occurrences
  (let [c (ev/run (expand/expand-expr '(let [f (code (fn [x] x))] (code [(esc f) (esc f)])) world/empty-root))
        {:keys [nodes]} (view/inspect c)
        functions (filterv #(= :fn (:op %)) nodes)
        first-fn (first functions) second-fn (second functions)
        other-body (:code (nth nodes (first (:children second-fn))))]
    (is (= 2 (count functions)))
    (is (thrown? clojure.lang.ExceptionInfo (view/rebuild (:at first-fn) [other-body])))
    (is (= (id c) (id (regenerate c))))))

(deftest binding-labels-describe-scope-without-constructing-it
  (let [c (source-code '(fn [x] (let [y x] (+ y x))))
        {:keys [nodes]} (view/inspect c)
        variables (filter #(= :var (:op %)) nodes)
        projection #(mapv (fn [d] (select-keys d [:op :binding :bindings :scope :children])) (:nodes %))]
    (is (= [0] (:bindings (first nodes))))
    (is (= #{0 1} (set (map :binding variables))))
    (is (every? #(contains? (set (:scope %)) (:binding %)) variables))
    (is (not-any? :name variables))
    (is (= (projection (view/inspect c)) (projection (view/inspect c))))))

(deftest boundaries-are-bounded-and-explicit
  (let [c (source-code '(fn [x] (+ x 1)))]
    (doseq [options [{:work 0} {:nodes 2} {:depth 0} {:unknown 1} {:nodes 1000}]]
      (is (thrown? clojure.lang.ExceptionInfo (view/inspect c options))))
    (let [{:keys [nodes]} (view/inspect c {:work 32}) root (first nodes) child (second nodes)]
      (is (= :budget-exhausted
             (try (dotimes [_ 100] (view/rebuild (:at root) [(:code child)])) nil
                  (catch clojure.lang.ExceptionInfo e (:reason (ex-data e)))))))
  (is (thrown? clojure.lang.ExceptionInfo (view/inspect (source-code '(fn [x] (code x))))))))

(deftest guest-walkers-generate-code-through-the-repl
  (let [s (repl/session {:source-roots ["examples/compat"]})
        r (repl/eval-response s "(require '[klara.residual]) (require '[klara.compiler]) (ns scratch) (def original (code (fn [x] (if false (/ 1 0) (let [y (+ x 1)] (* y y)))))) (def rebuilt (klara.residual/regenerate original)) (def simplified (klara.residual/prune-literal-branches original)) ((run simplified) 4)")
        root (world/snapshot (repl/current-world s))
        original (defs/lookup root 'scratch/original) rebuilt (defs/lookup root 'scratch/rebuilt)
        simplified (defs/lookup root 'scratch/simplified)]
    (is (empty? (:errors r))) (is (.endsWith ^String (:output r) "25"))
    (is (= (id original) (id rebuilt)))
    (is (not= (id original) (id simplified)))
    ;; Identity regeneration can prepare the original entry because its CoreID
    ;; is preserved. A genuinely rewritten function has a different identity.
    (is (empty? (:errors (repl/eval-response s "(def kernel (run original)) (klara.compiler/prepare-code rebuilt) (kernel 4)"))))
    (is (= "25" (repl/eval-string s "(kernel 4)")))
    (is (pos? (:hits (stage/stats (:cache s)))))
    (doseq [test [nil false 0 true [] {:a 1} ""]]
      (let [c (source-code (list 'fn '[x] (list 'if (list 'quote test) 'x '(/ 1 0))))
            _ (defs/define! (repl/current-world s) '(def scratch/choose (fn [source] (klara.residual/prune-literal-branches source))))
            f (:value (world/entry* (world/snapshot (repl/current-world s)) 'scratch/choose))
            pruned (binding [ev/*basis* (world/snapshot (repl/current-world s))] (ev/call-value f [c]))
            outcome (fn [code]
                      (try [:value ((ev/run (code/s->core (code/code-term code))) 7)]
                           (catch Throwable t [:error (class t)])))]
        (is (= (outcome c) (outcome pruned)))))))

(deftest mutual-tail-calls-are-interpreted-but-decline-compilation
  (let [w (world/make-world)]
    (defs/define! w '(def mutual (fn [n]
                                  (letfn [(even [i] (if (= i 0) true (odd (dec i))))
                                          (odd [i] (if (= i 0) false (even (dec i))))]
                                    (even n)))))
    (is (true? (defs/eval-form (world/snapshot w) '(mutual 10000))))
    (is (thrown? clojure.lang.ExceptionInfo (compiler/compile-def w 'mutual {:mode :baseline})))
    (is (thrown? clojure.lang.ExceptionInfo (compiler/compile-def w 'mutual {})))))
