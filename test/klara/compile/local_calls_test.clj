(ns klara.compile.local-calls-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.local-calls :as local] [klara.compile.core :as compiler]
            [klara.compile.prepare :as prepare] [klara.compile.budget :as budget]
            [klara.compile.staged :as staged] [klara.compile.service :as service]
            [klara.compile.core-test :refer [setup observe]]
            [klara.compile.unbox-test :refer [observation]]
            [klara.stage :as stage] [klara.world :as world] [klara.defs :as defs]
            [klara.eval :as ev] [klara.load :as load] [klara.repl :as repl]))

(def sample '(fn [n] (let [score (fn [x] (+ (* x x) 1))]
                      (loop [i 0 total 0]
                        (if (< i n) (recur (inc i) (+ total (score i))) total)))))
(def options {:mode :baseline :local-call-planner local/planner-symbol})
(defn ready [source] (let [w (setup source)] (local/bootstrap! w) w))
(defn reason [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest bounded-guest-analysis-opens-baseline-coverage
  (let [w (ready sample) b (budget/budget) cache (stage/make-cache)
        exe (compiler/compile-def w 'f (assoc options :budget b))]
    (is (some? (reason #(compiler/compile-def w 'f {:mode :baseline}))))
    (is (= 1 (get-in exe [:pass-log 2 :calls-inlined])))
    (is (= :local-call-inline-v1 (-> exe :rewrite-receipts first :rule)))
    (is (pos? (-> exe :rewrite-receipts first :transitions)))
    (is (= #{local/analysis-symbol local/planner-symbol} (set (map second (:compiler-reads exe)))))
    (is (not-any? #(#{local/analysis-symbol local/planner-symbol} (second %)) (:guards exe)))
    (is (< (:work (budget/usage b)) (:work budget/file-limits)))
    (stage/install! cache exe)
    (is (= [:value 333283345000 ""] (observe w '(f 10000) cache)))
    (is (pos? (:hits (stage/stats cache))))
    (is (zero? (:fallbacks (stage/stats cache))))))

(deftest recipe-preserves-types-errors-captures-and-nested-loops
  (doseq [source ['(fn [n salt] (let [score (fn [x] (+ (* x x) salt))]
                                  (loop [i 0 total 0]
                                    (if (< i n) (recur (inc i) (+ total (score i))) total))))
                  '(fn [n] (let [f (fn [x] (+ x 1))]
                             (loop [i 0 total 0]
                               (if (< i n)
                                 (recur (inc i) (+ total (loop [j 0 v 0]
                                                          (if (< j i) (recur (inc j) (+ v (f j))) v))))
                                 total))))
                  '(fn [n] (let [f (fn [x unused] x)] (f n (/ 1 0))))
                  '(fn [n] (let [triple (fn [x] (* x 3)) bump (fn [x] (+ x 1))]
                             (loop [i 0 total 0]
                               (if (< i n)
                                 (recur (inc i) (+ total (if (< i 2) (triple i) (bump i)))) total))))
                  '(fn [n] (let [f (fn [x] (let [n 99] (+ x n)))] (+ (f n) (f 2))))]]
    (let [w (ready source) exe (compiler/compile-def w 'f options)
          f (defs/lookup (world/snapshot w) 'f) cache (stage/make-cache)
          arity (count (second source))]
      (stage/install! cache exe)
      (doseq [n [0 1 4 4.5 9/2 4N nil :bad]
              salt (if (= arity 2) [1 1.5 1/2 Long/MAX_VALUE] [nil])
              :let [args (if (= arity 2) [n salt] [n])]]
        (is (= (observation f args (stage/make-cache)) (observation f args cache))
            (pr-str [source args]))))))

(deftest ordered-arguments-are-evaluated-once-even-if-unused
  (let [w (ready '(fn [probe] (let [pick (fn [a b] [a a])]
                              (pick (count probe) (count probe)))))
        exe (compiler/compile-def w 'f options) f (defs/lookup (world/snapshot w) 'f)
        cache (stage/make-cache) trace (atom [])
        probe (reify clojure.lang.Counted (count [_] (swap! trace conj :count) (count @trace)))
        expected (observation f [probe] (stage/make-cache))]
    (is (= [1 1] (nth expected 2)))
    (is (= [:count :count] @trace))
    (reset! trace [])
    (stage/install! cache exe)
    (is (= expected (observation f [probe] cache)))
    (is (= [:count :count] @trace))))

(def force-all
  '(fn [request] {:source-id (get request :source-id) :bindings (get request :candidates)}))

(deftest checker-rejects-invalid-proposals-before-emission
  (doseq [source ['(fn [n] (let [f (fn [x] (+ x 1))] f))
                  '(fn [n] (let [f (fn [x] (+ x 1))] [f]))
                  '(fn [n] (let [f (fn [x] (+ x 1))] (fn [x] (f x))))
                  '(fn [n] (let [f (fn [x] (+ x 1))] (f n 2)))]]
    (let [w (ready source) b (budget/budget)]
      (defs/define! w (list 'def local/planner-symbol force-all))
      (is (= :escaping-or-indirect-use
             (:check (reason #(compiler/compile-def w 'f (assoc options :budget b))))))
      (is (pos? (:work (budget/usage b))))
      (is (nil? (:emissions (budget/usage b))))))
  (doseq [planner ['(fn [r] {:source-id :wrong :bindings []})
                   '(fn [r] {:source-id (get r :source-id) :bindings [999]})
                   '(fn [r] {:source-id (get r :source-id) :bindings [1 1]})
                   '(fn [r] {:source-id (get r :source-id) :bindings [] :replacement :forged})]]
    (let [w (ready sample)]
      (defs/define! w (list 'def local/planner-symbol planner))
      (is (= :local-call-plan (:reason (reason #(compiler/compile-def w 'f options))))))))

(def touched (atom 0))
(defn touch [] (swap! touched inc))

(deftest pure-stepped-service-and-budget-boundaries
  (doseq [planner ['(fn [r] (klara.compile.local-calls-test/touch))
                   '(fn [r] (loop [] (recur)))]]
    (let [w (ready sample) b (budget/budget)]
      (defs/define! w (list 'def local/planner-symbol planner))
      (is (some? (reason #(compiler/compile-def w 'f (assoc options :budget b)))))
      (is (pos? (:work (budget/usage b))))
      (is (nil? (:emissions (budget/usage b))))))
  (is (zero? @touched))
  (let [w (ready sample) job (prepare/job {:local-call-planner local/planner-symbol
                                         :session-limits {:work 200}})
        cache (stage/make-cache)
        report (prepare/prepare! job (world/snapshot w) [{:name 'f :file :test}] cache)]
    (is (= :budget-exhausted (get-in report [:definitions 0 :reason])))
    (is (empty? (stage/executables cache))))
  (is (= :invalid-planner (:reason (reason #(prepare/job {:local-call-planner :invalid}))))))

(deftest residual-growth-is-bounded-before-emission
  (let [body (reduce (fn [t _] (list '+ t 1)) 'y (range 15))
        source (list 'fn '[x] (list 'let ['f (list 'fn '[y] body)]
                                    (vec (repeat 16 '(f x)))))
        w (ready source) b (budget/budget)
        failure (reason #(compiler/compile-def w 'f
                           (assoc options :budget b :definition-limits {:literal-bytes 16384}))) ]
    (is (= :budget-exhausted (:reason failure)))
    (is (= :nodes (:unit failure)))
    (is (pos? (:work (budget/usage b))))
    (is (nil? (:emissions (budget/usage b)))))
  ;; An optional planner must not impose its 128-node view cap on a function
  ;; with no local function bindings and no need to invoke that planner.
  (let [w (setup (list 'fn '[x] (vec (repeat 80 '(inc x)))))
        exe (compiler/compile-def w 'f (assoc options :local-call-planner 'absent))
        cache (stage/make-cache)]
    (stage/install! cache exe)
    (is (= [:value (vec (repeat 80 3)) ""] (observe w '(f 2) cache)))))

(deftest world-edits-do-not-revoke-independently-checked-output
  (let [w (ready sample) old (world/fork w) child (world/fork w)
        a (compiler/compile-def old 'f options) cache (stage/make-cache)]
    (defs/define! child (list 'def local/planner-symbol force-all))
    (let [b (compiler/compile-def child 'f options)]
      (is (not= (:compiler-reads a) (:compiler-reads b)))
      (stage/install! cache b)
      (is (= [:value 35 ""] (observe old '(f 5) cache)))
      (is (= [:value 35 ""] (observe child '(f 5) cache))))
    (defs/define! child (list 'def local/planner-symbol '(fn [r] {:source-id :wrong :bindings []})))
    (is (= :local-call-plan (:reason (reason #(compiler/compile-def child 'f options)))))
    (is (= [:value 35 ""] (observe child '(f 5) cache)))
    (is (some? (compiler/compile-def old 'f options)))))

(deftest before-use-job-and-shared-code-backend
  (let [w (world/make-world) _ (local/bootstrap! w) cache (stage/make-cache)
        job (prepare/job {:local-call-planner local/planner-symbol})
        report (load/load-string! w (pr-str (list 'def 'f sample))
                                 {:prepare :baseline :cache cache :preparation-job job})]
    (is (= :installed (get-in report [:preparation :definitions 0 :status])))
    (is (= [:value 35 ""] (observe w '(f 5) cache)))
    (is (pos? (:hits (stage/stats cache))))))

(deftest staged-planner-from-a-child-world-can-prepare-parent-code
  (let [w (ready sample)
        _ (load/load-file! w "examples/compat/klara/local_optimizer.cljc" {})
        old (world/fork w) child (world/fork w)
        _ (defs/define! child '(def alternate-planner
                               (run (klara.local-optimizer/planner-code 1))))
        root (world/snapshot child)
        source (defs/eval-form root (list 'code sample))
        p (staged/prevalidate (staged/prepare root source
                                             {:backend :baseline :local-call-planner 'alternate-planner}))
        info (staged/prepared-info p) cache (stage/make-cache)]
    (is (nil? (world/entry* (world/snapshot old) 'alternate-planner)))
    (is (= 'alternate-planner (-> info :rewrite-receipts first :planner)))
    (is (= #{'alternate-planner 'klara.local-optimizer/uses} (set (map second (:compiler-reads info)))))
    (is (empty? (stage/executables cache)))
    ;; The planner is absent in the parent. Its independently checked decision
    ;; needs no operational lookup of that planner after publication.
    (is (= :installed (:status (staged/install! cache (world/snapshot old) p))))
    (is (= [:value 35 ""] (observe old '(f 5) cache)))
    (is (pos? (:hits (stage/stats cache))))))

(deftest integer-compiler-data-retains-its-representation
  (let [w (world/make-world)]
    (defs/define! w '(def echo (fn [value] value)))
    (doseq [x [(Integer/valueOf 2) 2]]
      (let [r (service/invoke (budget/budget) (world/snapshot w) 'echo [x] 100)]
        (is (= (class x) (class (:value r))))
        (is (= x (:value r)))))))

(deftest guest-staging-and-actual-authority-fork-use-the-same-path
  (let [s (repl/session {:source-roots ["examples/compat"]})
        r (repl/eval-response s
            (str "(require '[klara.local-optimizer]) "
                 "(def source (code " (pr-str sample) ")) "
                 "(def f (run source)) "
                 "(klara.local-optimizer/prepare-code source) (f 5)"))]
    (is (empty? (:errors r)))
    (is (.endsWith ^String (:output r) "35"))
    (is (pos? (:hits (stage/stats (:cache s)))))
    (is (zero? (:fallbacks (stage/stats (:cache s)))))))
