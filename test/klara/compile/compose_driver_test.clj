(ns klara.compile.compose-driver-test
  (:require [clojure.test :refer [deftest is]] [klara.compile.compose :as compose]
            [klara.compile.core :as compiler] [klara.compile.prepare :as prepare]
            [klara.compile.local-calls :as local] [klara.compile.budget :as budget]
            [klara.compile.edge :as edge] [klara.compile.subject :as subject]
            [klara.compile.core-test :refer [setup observe]]
            [klara.stage :as stage] [klara.core :as core] [klara.world :as world]))

(def nested-source
  '(fn [n] (let [square (fn [x] (* x x)) score (fn [x] (+ (square x) 1))]
             (loop [i 0 total 0] (if (< i n) (recur (inc i) (+ total (score i))) total)))))

(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest successive-checked-rounds-accelerate-original-entry
  (let [w (setup nested-source) _ (local/bootstrap! w)
        opts {:mode :baseline :local-call-planner local/planner-symbol}
        b (budget/budget) exe (compiler/compile-def w 'f (assoc opts :budget b))
        receipts (:rewrite-receipts exe) cache (stage/make-cache)]
    (is (some? (failure #(compiler/compile-def w 'f (assoc opts :rewrite-rounds 1)))))
    (is (= 2 (count receipts)))
    (is (= (:target-id (first receipts)) (:source-id (second receipts))))
    (is (= {:rounds 2 :stop :round-limit :calls-inlined 2} (:rewrite-summary exe)))
    (is (< (:work (budget/usage b)) (:work budget/file-limits)))
    (stage/install! cache exe)
    (doseq [form ['(f 0) '(f 5) '(f 5.5) '(f nil) '(f :bad)]]
      (is (= (observe w form (stage/make-cache)) (observe w form cache))))
    (is (pos? (:hits (stage/stats cache))))
    (is (zero? (:fallbacks (stage/stats cache))))))

(deftest zero-call-elimination-still-needs-successive-rounds
  (let [w (setup '(fn [x] (let [helper (fn [y] (+ y 1)) unused (fn [] helper)] x)))
        _ (local/bootstrap! w)
        exe (compiler/compile-def w 'f {:mode :baseline :local-call-planner local/planner-symbol})
        cache (stage/make-cache)]
    (is (= 2 (count (:rewrite-receipts exe))))
    (is (zero? (get-in exe [:rewrite-summary :calls-inlined])))
    (stage/install! cache exe)
    (is (= [:value 7 ""] (observe w '(f 7) cache)))))

(deftest malformed-or-cyclic-links-decline
  (let [a (core/quote* 1) b (core/quote* 2) c (core/quote* 3)
        issue (edge/trusted-issuer :test-controller subject/core-contract {:method :test-only})
        step (fn [target accepted] (fn [_] {:term target :edge accepted :compiler-reads #{}}))]
    (doseq [[f check] [[(fn [_] {:term b :receipt {:source-id (core/code-id a) :target-id (core/code-id b)}}) :unchecked-edge]
                       [(step b (issue c b {})) :source-or-target]
                       [(step c (issue a b {})) :source-or-target]
                       [(fn [t] (let [target (if (= t a) b a)]
                                  {:term target :edge (issue t target {})})) :cycle]]]
      (is (= check (:check (failure #(compose/run (budget/budget) a f identity 4))))))
    (is (= :invalid-rewrite-rounds (:reason (failure #(prepare/job {:rewrite-rounds 5})))))))
