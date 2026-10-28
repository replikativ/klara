(ns klara.compile.core-test
  "Differential compiler tests: T0 is the oracle, including errors and
  traces. Generated inputs use a fixed seed for reproducible failures."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.core :as cc] [klara.compile.ir :as ir]
            [klara.compile.escape :as escape] [klara.compile.pe :as pe]
            [klara.world :as w] [klara.defs :as d] [klara.eval :as ev]
            [klara.core :as c] [klara.expand :as x] [klara.stage :as stage]
            [klara.repl :as repl] [klara.authority :as auth]))

(defn setup [form]
  (let [world (w/make-world)] (d/define! world (list 'def 'f form)) world))
(defn observe [world form cache]
  (let [out (java.io.StringWriter.)]
    (binding [auth/*store* (auth/new-store) *out* out]
      (try
        (let [v (stage/with-cache cache
                  (ev/run (x/expand-expr form (w/snapshot world)) {:basis (w/snapshot world)}))]
          [:value v (str out)])
        (catch Throwable t [:error (repl/error-kind t) (str out)])))))

(def programs
  ['(fn [n] (+ (* n n) 3))
   '(fn [n] (if 0 (+ n 1) (/ 1 0)))
   '(fn [n] (let [a n b a] (+ b 2)))
   '(fn [n] (loop [i n acc 0] (if (> i 0) (recur (dec i) (+ acc i)) acc)))
   '(fn [n] (let [v [n (+ n 1)]] (+ (first v) (second v))))
   '(fn [n] (let [m {:a n :b (+ n 1)}] (+ (get m :a) (get m :b))))
   '(fn [n] (let [f (fn [a] (+ a n))] (+ (f 2) (f 3))))
   '(fn [n] ((fn [x] ((fn [x] (+ x 1)) x)) n))
   '(fn [n] (handle [h {:weight (fn [x k] (k (* x 2)))}]
              (+ (perform h :weight n) (perform h :weight (+ n 1)))))
   '(fn [n] (handle [h {:stop (fn [x k] (+ x 10))}]
              (+ (perform h :stop n) (/ 1 0))))
   '(fn [n] (/ 10 n))
   '(fn [n] (let [v [(/ 1 n) 7]] (second v)))])

(deftest differential-corpus
  (doseq [program programs]
    (testing (pr-str program)
      (let [world (setup program) cache (stage/make-cache)
            exe (cc/compile-def world 'f {}) random (java.util.Random. 88)]
        (is (= :tested (get-in exe [:certificate :kind])))
        (stage/install! cache exe)
        (doseq [n (concat [0 1 -1 30] (repeatedly 30 #(- (.nextInt random 40) 10)))]
          (is (= (observe world (list 'f n) (stage/make-cache))
                 (observe world (list 'f n) cache))))))))

(deftest guards-redefinition-and-deletion
  (let [world (w/make-world) cache (stage/make-cache)]
    (d/define! world '(def helper (fn [x] (+ x 1))))
    (d/define! world '(def f (fn [x] (* (helper x) 2))))
    (let [exe (cc/compile-def world 'f {}) old (w/fork world)]
      (stage/install! cache exe)
      (is (some #(= [:world 'helper (:value-id (w/entry* (w/snapshot world) 'helper))] %) (:guards exe)))
      (is (= [:value 8 ""] (observe world '(f 3) cache)))
      (d/define! world '(def helper (fn [x] (+ x 100))))
      (is (= [:value 206 ""] (observe world '(f 3) cache)))
      (is (pos? (:fallbacks (stage/stats cache))))
      (is (= [:value 8 ""] (observe old '(f 3) cache)))
      (let [before (observe world '(f 3) cache)]
        (stage/clear! cache)
        (is (= before (observe world '(f 3) cache)))))))

(deftest fallback-context-and-arity
  (let [world (setup '(fn [x] (+ 10 (/ 1 x)))) cache (stage/make-cache)]
    (stage/install! cache (cc/compile-def world 'f {}))
    (doseq [form ['(f) '(f 1 2)
                  '(handle :dynamic {:exn/raise (fn [e k] (k 2))} (f 0))
                  '(let [r (resource :ok)] (fork [b (f 2) c (f 4)] (adopt! b)))]]
      (is (= (observe world form (stage/make-cache)) (observe world form cache))))))

(deftest escape-soundness
  (doseq [program ['(fn [f x] (let [v [x]] (f v)))
                   '(fn [x] (let [v [x]] (identity (mapv identity v))))
                   '(fn [x] (let [v [x]] (fn [] (first v))))
                   '(fn [x] (let [v [x] alias v] alias))]]
    (let [t (:term (pe/run (ir/named (x/expand-expr program w/empty-root)) 10))
          a (escape/run t)]
      (is (zero? (:allocations-removed a)))
      (is (some :escapes? (:bindings a)))))
  ;; An unknown function retains the vector, not just the projected field.
  (let [world (setup '(fn [f x] (let [v [x (+ x 1)]] (do (f v) (first v)))))
        retained (atom nil) f (:value (w/entry* (w/snapshot world) 'f))]
    (is (thrown? clojure.lang.ExceptionInfo (cc/compile-def world 'f {})))
    (is (= 4 (ev/call-value f [(fn [v] (reset! retained v)) 4])))
    (is (= [4 5] @retained))))

(deftest unsupported-control-stays-in-t0
  (doseq [program ['(fn [x] (handle [h {:choose (fn [k] (+ (k 1) (k 2)))}] (+ x (perform h :choose))))
                   '(fn [x] (println x))
                   '(fn [x] (fn [] x))]]
    (is (thrown? clojure.lang.ExceptionInfo (cc/compile-def (setup program) 'f {})))))

(deftest effect-order-trace
  (let [world (setup '(fn [x y]
                       (handle [h {:op (fn [v k] (k (count v)))}]
                         [(perform h :op x) (perform h :op y)])))
        trace (atom [])
        counted (fn [label n] (reify clojure.lang.Counted
                               (count [_] (swap! trace conj label) n)))
        x (counted :first 7) y (counted :second 8)
        form (list 'f (list 'quote x) (list 'quote y))
        cache (stage/make-cache)]
    (stage/install! cache (cc/compile-def world 'f {}))
    (let [a (observe world form (stage/make-cache)) ta @trace]
      (reset! trace [])
      (is (= a (observe world form cache)))
      (is (= [:first :second] ta @trace)))))

(deftest authority-contexts
  (let [world (setup '(fn [e] (do (spend! e 1/4) (remaining e))))
        cache (stage/make-cache)]
    (stage/install! cache (cc/compile-def world 'f {}))
    (doseq [form ['(let [e (evidence 1)] [(f e) (remaining e)])
                  '(let [e (evidence 1)]
                     (fork [b (f e) c (f e)] (adopt! b))
                     (remaining e))
                  '(let [e (evidence 1/8)] (f e))]]
      (is (= (observe world form (stage/make-cache)) (observe world form cache))))))

(deftest definition-time-inlined-reads
  (let [world (w/make-world) cache (stage/make-cache)]
    (d/define! world '(def helper (fn [x] (+ x 1))))
    (d/define! world '(def f (fn [x] (helper x))))
    (stage/install! cache (cc/compile-def world 'f {}))
    (stage/with-cache cache (d/define! world '(def derived (f 3))))
    (is (some #(and (= :value (first %)) (= 'helper (second %)))
              (:reads (w/entry* (w/snapshot world) 'derived))))
    (d/define! world '(def helper (fn [x] (+ x 100))))
    (d/invalidate! world 'helper)
    (is (= 103 (:value (w/entry* (w/snapshot world) 'derived))))))

(deftest alias-and-liveness-port
  (let [term (ir/named (x/expand-expr '(let [a [1] b a c b] (first c)) w/empty-root))
        analysis (escape/analyze-let term)
        names (set (map :binding (:bindings analysis)))]
    (is (= 3 (count names)))
    (is (every? #(= names (:aliases %)) (:bindings analysis)))
    (is (not-any? :last-use? (:bindings analysis))))
  (is (= #{'a 'b 'c} (escape/alias-closure #{'a} {'a #{'b} 'b #{'a 'c} 'c #{'b}}))))

(deftest r3-all-programs
  (doseq [program programs]
    (let [world (setup program) cache (stage/make-cache)]
      (stage/install! cache (cc/compile-def world 'f {}))
      (let [before (observe world '(f 4) cache)]
        (is (pos? (:hits (stage/stats cache))))
        (stage/clear! cache)
        (is (= before (observe world '(f 4) cache)))))))

(deftest traces-before-failure-and-abort
  (doseq [program ['(fn [x y] (let [v [(count x) (/ 1 0)]] (first v)))
                   '(fn [x y] (handle [h {:stop (fn [v k] (count v))}]
                                [(perform h :stop x) (count y)]))]]
    (let [world (setup program) cache (stage/make-cache) trace (atom [])
          counted (fn [label] (reify clojure.lang.Counted (count [_] (swap! trace conj label) 1)))
          form (list 'f (list 'quote (counted :first)) (list 'quote (counted :second)))]
      (stage/install! cache (cc/compile-def world 'f {}))
      (let [a (observe world form (stage/make-cache)) ta @trace]
        (reset! trace [])
        (is (= a (observe world form cache)))
        (is (= [:first] ta @trace))))))

(deftest boxed-vector-projection-keys
  (doseq [key [(short 0) (byte 0) 0N (biginteger 0) (int 0) 0]]
    (let [program (list 'fn ['x] (list 'let ['v ['x]] (list 'get 'v (list 'quote key))))
          world (setup program) cache (stage/make-cache)]
      (stage/install! cache (cc/compile-def world 'f {}))
      (is (= (observe world '(f 42) (stage/make-cache)) (observe world '(f 42) cache))))))
