(ns interpreter.bridge-checks
  (:require [clojure.test :refer [deftest is]]
            [interpreter.bridge :as b] [interpreter.mutable :as m]
            [interpreter.mutable-checks :as checks]
            [klara.eval :as ev] [klara.expand :as x] [klara.world :as w]
            [klara.core :as core] [klara.defs :as defs] [klara.authority :as authority])
  (:import [java.util IdentityHashMap]))

(defn signature
  "Normalize a reachable pure CEK graph, preserving closure aliases/cycles.
   This observer is tested implementation code, not a checked semantics."
  [[mode control env k extra] basis]
  (let [seen (IdentityHashMap.)]
    (letfn [(value [v]
              (cond
                (ev/closure? v)
                (if-let [id (.get seen v)] [:ref id]
                  (let [id (.size seen)]
                    (.put seen v id)
                    [:closure id (ev/closure-term v)
                     (identical? basis (ev/closure-basis v))
                     (mapv value (ev/closure-locals v))]))
                (vector? v) [:vector (mapv value v)]
                (instance? Double v) [:double (Double/doubleToRawLongBits (double v))]
                (instance? java.math.BigDecimal v)
                [:decimal (.unscaledValue ^java.math.BigDecimal v) (.scale ^java.math.BigDecimal v)]
                :else [:scalar (class v) v]))
            (environment [env]
              (when env [(identical? basis (:basis env))
                         (identical? basis (:mint env)) (mapv value (:locals env))]))
            (frame [f]
              (case (:tag f)
                :let [:let (:body f) (environment (:env f))]
                :if [:if (:node f) (environment (:env f))]
                :list [:list (:node f) (environment (:env f))
                       (mapv value (:vals f)) (vec (:todo f))]))]
      (if (= :finish mode)
        [mode control (mapv value env) (environment k) (mapv frame extra)]
        [mode (if (= mode :ret) (value control) control)
         (environment env) (mapv frame k)]))))

(defn- terminal? [state] (and (= :ret (first state)) (empty? (nth state 3))))

(defn- reference-entry [term args basis]
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
    (let [f (ev/run term {:basis basis})]
      (ev/call-value* f args {:locals [] :basis basis :mint basis} '()))))

(defn compare-trajectory
  ([form n] (compare-trajectory form n b/prepare 20))
  ([form n prepare reference-gap]
  (let [basis w/empty-root term (x/expand-expr form basis)
        artifact (prepare term) private (b/start artifact [n])
        expected ((ev/run term) n)]
    (loop [reference (reference-entry term [n] basis) private-steps 0 reference-steps 0]
      (assert (< private-steps 3000) "bounded test exceeded private transition limit")
      (let [snapshot (b/freeze private)
            materialized (b/transfer! (b/thaw snapshot)) target (signature (:state materialized) basis)
            [reference advanced]
            (loop [r reference steps 0]
              (assert (< steps reference-gap) (str "no nearby reference state at private step " private-steps))
              (if (= target (signature r basis)) [r steps]
                (do (assert (not (terminal? r)) "reference ended before matching state")
                    (recur (ev/step-state r) (inc steps)))))]
        (is (= expected (b/resume! materialized true)))
        (is (= expected (b/resume! (b/transfer! (b/thaw snapshot)) false)))
        (if (= :done (b/advance! private 1))
          ;; Also compare the final state, including the retained lexical prefix.
          (let [final (b/transfer! private)
                terminal (loop [r reference]
                           (if (terminal? r) r (recur (ev/step-state r))))]
            (is (= (signature terminal basis) (signature (:state final) basis)))
            (is (= expected (b/resume! final)))
            {:private-steps (inc private-steps) :reference-steps (+ reference-steps advanced)})
          (recur reference (inc private-steps) (+ reference-steps advanced))))))))

(deftest every-private-pause-matches-a-reachable-reference-configuration
  (doseq [form checks/programs n [0 3]]
    (compare-trajectory form n)))

(deftest numeric-representations-survive-every-pause
  (binding [*math-context* (java.math.MathContext. 8)]
    (doseq [n [1N 1.00M -0.0 0.0]]
      (compare-trajectory '(fn [n] (/ n 3)) n))))

(deftest partially-evaluated-operands-are-resumed-at-their-current-position
  (let [term (x/expand-expr '(fn [n] (+ 10 (* n 2) 3)) w/empty-root)
        capsule (b/start (b/prepare term) [4])]
    (b/advance! capsule 8)
    (let [transfer (b/transfer! capsule)
          [mode value _ k] (:state transfer) frame (first k)]
      (is (= :ret mode)) (is (= 8 value))
      (is (= [10] (:vals frame)))
      (is (= [{:op :quote :datum 3}] (vec (:todo frame))))
      (is (= 21 (b/resume! transfer))))))

(deftest aliases-recursive-capture-groups-and-source-metadata-survive
  (let [term (x/expand-expr
               '(fn [n] (letfn [(f [x] (if (zero? x) n (g (dec x))))
                               (g [x] (if (zero? x) n (f (dec x))))]
                          (f 4))) w/empty-root)
        ;; Function metadata survives through the original-Core identity index.
        term (update-in term [:body :inits 0] with-meta {:bridge/source :first-function})
        c (b/start (b/prepare term) [9])]
    (b/advance! c 2)
    (let [[_ _ env] (:state (b/transfer! c))
          f (nth (:locals env) 1) g (nth (:locals env) 2)
          captured (ev/closure-locals f)]
      (is (identical? captured (ev/closure-locals g)))
      (is (identical? f (nth captured 1)))
      (is (identical? g (nth captured 2)))
      (is (= :first-function (:bridge/source (meta (ev/closure-term f)))))))
  (let [term (x/expand-expr '(fn [n] (let [f (fn [] n) g f] (+ (f) (g)))) w/empty-root)
        c (b/start (b/prepare term) [7])]
    ;; Find the first state whose active locals contain both aliases.
    (loop []
      (let [snap (b/freeze c) state (:state (b/transfer! (b/thaw snap)))
            locals (:locals (nth state 2))]
        (if (= 3 (count locals))
          (is (identical? (nth locals 1) (nth locals 2)))
          (do (b/advance! c 1) (recur)))))))

(deftest pinned-code-basis-and-entry-decimal-context-are-retained
  (let [world (w/make-world) _ (defs/define! world '(def marker :old))
        old (w/snapshot world)
        term (x/expand-expr '(fn [n] (let [f (fn [] n)] (f))) old)
        c (b/start (b/prepare term {:basis old}) [4])]
    (defs/define! world '(def marker :new))
    (b/advance! c 2)
    (let [[_ f env] (:state (b/transfer! c))]
      (is (identical? old (:basis env)))
      (is (identical? old (ev/closure-basis f)))))
  (let [a (b/prepare (x/expand-expr '(fn [] (/ 1M 3M)) w/empty-root))
        c (binding [*math-context* (java.math.MathContext. 3)] (b/start a [])) snap (b/freeze c)]
    (binding [*math-context* (java.math.MathContext. 6)]
      (is (= 0.333M (b/resume! (b/transfer! (b/thaw snap)))))
      (b/advance! c 100)
      (is (= 0.333M (b/resume! (b/transfer! c))))
      (is (= 0.333333M (b/resume! (b/transfer! (b/start a []))))))))

(deftest transfer-and-resumption-consume-their-api-leases
  (let [c (b/start (b/prepare (x/expand-expr '(fn [n] (+ n 1)) w/empty-root)) [4])
        transfer (b/transfer! c)]
    (is (= :transferred (b/status c)))
    (is (thrown? clojure.lang.ExceptionInfo (b/advance! c 1)))
    (is (thrown? clojure.lang.ExceptionInfo (b/transfer! c)))
    (is (thrown? clojure.lang.ExceptionInfo (b/freeze c)))
    (is (= 5 (b/resume! transfer)))
    (is (thrown? clojure.lang.ExceptionInfo (b/resume! transfer)))))

(deftest materialized-state-does-not-retain-reusable-working-buffers
  (let [term (x/expand-expr (first checks/programs) w/empty-root)
        c (b/start (b/prepare term) [20]) _ (b/advance! c 30)
        ;; Keep a raw reference only to stress detachment. The capsule API
        ;; prohibits advancing this machine after its transfer.
        retired (:machine @(:life c)) transfer (b/transfer! c)
        before (signature (:state transfer) w/empty-root)]
    (is (= 190 (m/run! retired)))
    (is (= before (signature (:state transfer) w/empty-root)))
    (is (= 190 (b/resume! transfer)))))

(deftest snapshot-resumptions-on-other-threads-retain-the-entry-contract
  (let [term (x/expand-expr '(fn [] (/ 1M 3M)) w/empty-root)
        c (binding [*math-context* (java.math.MathContext. 3)] (b/start (b/prepare term) []))
        snapshot (b/freeze c)
        runs (mapv (fn [precision]
                     (future
                       (binding [*math-context* (java.math.MathContext. precision)]
                         (b/resume! (b/transfer! (b/thaw snapshot)))))) [6 9])]
    (is (= [0.333M 0.333M] (mapv deref runs)))
    (is (= :paused (b/status c))))
  (let [c (b/start (b/prepare (x/expand-expr '(fn [n] (+ n 1)) w/empty-root)) [4])
        gate (promise)
        claim #(future @gate (try {:transfer (b/transfer! c)}
                                 (catch clojure.lang.ExceptionInfo t {:decline (ex-data t)})))
        a (claim) b (claim) _ (deliver gate true) results [@a @b]
        accepted (keep :transfer results)]
    (is (= 1 (count accepted)))
    (is (= 1 (count (keep :decline results))))
    (is (= 5 (b/resume! (first accepted))))))

(deftest initialization-is-retained-and-unsupported-authority-is-not-minted
  (let [term (x/expand-expr '(let [v (/ 1M 3M)] (fn [] v)) w/empty-root)
        artifact (binding [*math-context* (java.math.MathContext. 3)] (b/prepare term))]
    (binding [*math-context* (java.math.MathContext. 6)]
      (is (= 0.333M (b/resume! (b/transfer! (b/start artifact [])))))))
  (let [store (authority/new-store) before @store
        term (x/expand-expr '(let [r (resource :unused)] (fn [] 42)) w/empty-root)]
    (binding [authority/*store* store]
      (is (thrown? clojure.lang.ExceptionInfo (b/prepare term)))
      (is (= before @store)))))

(deftest incompatible-primitives-errors-and-unsupported-contexts-decline
  (let [a (b/prepare (x/expand-expr '(fn [n] (+ n 1)) w/empty-root)) c (b/start a [1])
        called (atom false)]
    (with-redefs [core/prims (assoc core/prims '+ (fn [& _] (reset! called true)))]
      (is (thrown? clojure.lang.ExceptionInfo (b/transfer! c)))
      (is (= :paused (b/status c))) (is (false? @called)))
    (is (= 2 (b/resume! (b/transfer! c)))))
  (let [term (x/expand-expr '(fn [n] (+ n 1)) w/empty-root)
        a (b/prepare term) c (b/start a [Long/MAX_VALUE]) transfer (b/transfer! c)]
    (is (thrown? ArithmeticException (b/resume! transfer)))
    (is (= :failed @(:life transfer)))
    (is (thrown? clojure.lang.ExceptionInfo (b/resume! transfer)))
    (is (thrown? clojure.lang.ExceptionInfo (b/prepare term {:mint nil})))))
