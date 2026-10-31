(ns klara.compile.baseline-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.core :as compiler] [klara.compile.baseline :as baseline]
            [klara.compile.budget :as budget] [klara.compile.prepare :as prepare]
            [klara.compile.guest :as guest] [klara.compile.loop :as transfer]
            [klara.compile.staged :as staged] [klara.compile.unbox :as unbox]
            [klara.compile.speculate :as speculate] [klara.compile.escape :as escape]
            [klara.affine :as affine] [klara.compile.pe :as pe]
            [klara.compile.core-test :refer [setup observe]]
            [klara.code :as code] [klara.core :as core] [klara.defs :as defs]
            [klara.eval :as ev] [klara.expand :as expand] [klara.load :as load]
            [klara.stage :as stage] [klara.world :as world] [klara.repl :as repl]))

(deftest mandatory-only-full-calls
  (let [forbidden (fn [& _] (throw (Exception. "optional pass ran")))]
    (with-redefs [speculate/run forbidden pe/run forbidden escape/run forbidden
                  affine/check forbidden unbox/loop-kinds forbidden unbox/return-layout forbidden]
      (doseq [program ['(fn [x] (let [y (+ x 1)] (if (< y 0) (- y) (* y y))))
                       '(fn [n] (loop [i n a [1] b [2]]
                                  (if (> i 0) (recur (dec i) b (conj a i)) a)))
                       '(fn [x] (if x 7 (/ 1 0)))
                       '(fn [x] (+ x 1))]]
        (let [w (setup program) cache (stage/make-cache)
              exe (compiler/compile-def w 'f {:mode :baseline})]
          (stage/install! cache exe)
          (doseq [arg [nil false 0 2 -2 3.5 2N]]
            (is (= (observe w (list 'f arg) (stage/make-cache))
                   (observe w (list 'f arg) cache))))
          (is (zero? (:deopts (stage/stats cache)))))))))

(deftest shared-code-lifecycle
  (let [source (code/->code (code/core->s (expand/expand-expr
                                         '(fn [x] (conj x :done)) world/empty-root)))
        p (staged/prevalidate (staged/prepare world/empty-root source {:backend :baseline}))
        cache (stage/make-cache)]
    (is (= :installed (:status (staged/install! cache world/empty-root p))))
    (is (= [:start :done]
           (stage/with-cache cache
             (ev/call-value (ev/run (code/s->core (code/code-term source))) [[:start]]))))
    (is (zero? (:deopts (stage/stats cache))))))

(deftest direct-loop-lowering-preserves-generic-behavior
  (doseq [program ['(fn [x] (loop [i 0 acc 0]
                             (if (< i 3) (recur (inc i) (+ acc x)) acc)))
                   '(fn [x] (loop [i x a 1 b 2]
                              (if (> i 0) (recur (dec i) b (+ a b)) a)))
                   '(fn [x] (loop [a (/ 1 x) b (nth [] 0)] a))
                   '(fn [x] (loop [i 0 acc 9223372036854775807]
                              (if (< i x) (recur (inc i) (+ acc 1)) acc)))]]
    (let [w (setup program) cache (stage/make-cache)
          exe (compiler/compile-def w 'f {:mode :baseline})]
      (is (some #{'clojure.core/loop} (tree-seq coll? seq (:form exe))))
      (is (not-any? #{'clojure.core/letfn} (tree-seq coll? seq (:form exe))))
      (stage/install! cache exe)
      (doseq [x [nil false -1 0 1 3 3.5 3N 2/3]]
        (let [reference (observe w (list 'f x) (stage/make-cache))
              actual (observe w (list 'f x) cache)]
          (is (= reference actual))
          (when (= :value (first actual))
            (is (= (core/code-id (second reference)) (core/code-id (second actual)))))))
      (is (zero? (:deopts (stage/stats cache)))))))

(deftest dependency-memo-and-pinned-worlds
  (let [w (world/make-world) cache (stage/make-cache) b (budget/budget)]
    (doseq [form ['(def leaf (fn [x] (+ x 1)))
                  '(def a (fn [x] (leaf x))) '(def b (fn [x] (leaf x)))
                  '(def f (fn [x] (+ (a x) (b x))))]] (defs/define! w form))
    (let [old (world/fork w) exe (compiler/compile-def w 'f {:mode :baseline :budget b})]
      (is (= 4 (:emissions (budget/usage b))))
      (stage/install! cache exe)
      (is (= [:value 6 ""] (observe old '(f 2) cache)))
      (defs/define! w '(def leaf (fn [x] (+ x 10))))
      (is (= [:value 24 ""] (observe w '(f 2) cache)))
      (is (= [:value 6 ""] (observe old '(f 2) cache))))))

(deftest budgets-and-loader
  (let [w (world/make-world) cache (stage/make-cache)
        job (prepare/job {:session-limits {:emissions 1}})]
    (is (nil? (:preparation (load/load-string! w "(def x 1)"))))
    (let [r (load/load-string! w "(def f (fn [x] (+ x 1))) (def g (fn [x] (* x 2)))"
                               {:prepare :baseline :cache cache :preparation-job job})]
      (is (= 2 (:forms r)))
      (is (= [:installed :declined] (mapv :status (filter :name (get-in r [:preparation :definitions])))))
      (is (= 1 (:emissions (budget/usage (:budget job)))))
      (is (= 8 (defs/eval-form (world/snapshot w) '(g 4)))))
    (let [r (load/load-string! w "(def h (fn [x] (- x 1)))"
                               {:prepare :baseline :cache cache :preparation-job job})]
      (is (= :budget-exhausted (get-in r [:preparation :definitions 0 :reason])))
      (is (= 3 (defs/eval-form (world/snapshot w) '(h 4)))))))

(deftest declines-retain-work
  (let [w (setup '(fn [x] (f x))) b (budget/budget)]
    (is (thrown? clojure.lang.ExceptionInfo (compiler/compile-def w 'f {:mode :baseline :budget b})))
    (is (pos? (:work (budget/usage b))))
    (is (nil? (:emissions (budget/usage b)))))
  (doseq [p ['(fn [f x] (f x)) '(fn [x] (code (+ 1 x)))
             '(fn [x] (perform :host/call x))]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (compiler/compile-def (setup p) 'f {:mode :baseline})))))

(deftest guest-plan-is-consumed-and-checked
  (let [w (setup '(fn [n] (loop [i n a 1 b 2]
                           (if (> i 0) (recur (dec i) b (+ a b)) a))))
        exe (compiler/compile-def w 'f {:mode :baseline}) cache (stage/make-cache)]
    (is (seq (:transfer-receipts exe)))
    (is (every? #(= :klara-baseline (:producer %)) (:transfer-receipts exe)))
    (stage/install! cache exe)
    (is (= [:value 13 ""] (observe w '(f 5) cache)))
    (is (pos? (:hits (stage/stats cache))))
    (is (zero? (:deopts (stage/stats cache))))
    (with-redefs [guest/producer (fn [& _] (fn [destinations arguments]
                                         (update (transfer/transfer destinations arguments)
                                                 :commits #(vec (reverse %)))))]
      (is (thrown? clojure.lang.ExceptionInfo
                   (compiler/compile-def w 'f {:mode :baseline}))))))

(deftest bounded-code-and-no-refunds
  (doseq [limits [{:work -1} {:work 0.5} {:unknown 1}]]
    (is (thrown? clojure.lang.ExceptionInfo (budget/budget limits))))
  (is (thrown? clojure.lang.ExceptionInfo (budget/charge! (budget/budget) :work -1)))
  (let [text (apply str (repeat 300 "x"))
        source (core/lam 0 (core/prim 'vector (core/quote* text) (core/quote* text) (core/quote* text)))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"budget exhausted"
                         (baseline/scan! source budget/definition-limits))))
  (let [source (code/->code (code/core->s (expand/expand-expr '(fn [x] (+ x 1)) world/empty-root)))
        b (budget/budget {:work 0})]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"budget exhausted"
                         (staged/prepare world/empty-root source {:backend :baseline :budget b}))))
  (let [w (world/make-world) job (prepare/job {:session-limits {:work 0}})
        r (prepare/prepare! job (world/snapshot w)
                            (vec (repeat 10000 {:name 'absent :file :test})) (stage/make-cache))]
    (is (= 2 (count (:definitions r))))
    (is (= 9999 (:remaining (last (:definitions r)))))))

(deftest primitive-root-and-overflow
  (let [w (setup '(fn [x] (+ x 1))) cache (stage/make-cache)]
    (stage/install! cache (compiler/compile-def w 'f {:mode :baseline}))
    (is (= (observe w (list 'f Long/MAX_VALUE) (stage/make-cache))
           (observe w (list 'f Long/MAX_VALUE) cache)))
    (with-redefs [clojure.core/+ (fn [& _] :wrong)]
      (is (= [:value 3 ""] (observe w '(f 2) cache))))
    (is (pos? (:fallbacks (stage/stats cache))))))

(def ^:dynamic *load-target* nil)
(def ^:dynamic *initializations* nil)
(defn initializer [] (swap! *initializations* inc) 7)
(defn conflicting-initializer []
  (swap! *initializations* inc)
  (defs/define! *load-target* '(def concurrent 9))
  7)

(deftest loader-never-replays-for-preparation
  (binding [*initializations* (atom 0)]
    (let [w (world/make-world) cache (stage/make-cache)]
      (load/load-string! w "(def x (klara.compile.baseline-test/initializer)) (def f (fn [x] (+ x 1)))"
                         {:prepare :baseline :cache cache})
      (is (= 1 @*initializations*))
      (is (= 7 (defs/lookup (world/snapshot w) 'x)))
      (binding [*load-target* w]
        (let [before (count (stage/executables cache))]
          (is (thrown? clojure.lang.ExceptionInfo
                       (load/load-string! w "(def uncommitted (klara.compile.baseline-test/conflicting-initializer))"
                                          {:prepare :baseline :cache cache})))
          (is (= before (count (stage/executables cache))))
          (is (= 2 @*initializations*))
          (is (nil? (world/entry* (world/snapshot w) 'uncommitted))))))))

(deftest session-loads-share-the-allowance
  (let [s (repl/session {:prepare :baseline :session-limits {:emissions 1}})
        w (repl/current-world s) options (repl/load-options s)]
    (is (= :installed (get-in (load/load-string! w "(def first-fn (fn [x] (+ x 1)))" options)
                              [:preparation :definitions 0 :status])))
    (is (= :budget-exhausted
           (get-in (load/load-string! w "(def second-fn (fn [x] (+ x 2)))" (repl/load-options s))
                   [:preparation :definitions 0 :reason])))
    (is (= "3" (repl/eval-string s "(second-fn 1)")))))
