(ns klara.compile.direct-abi-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.core :as cc] [klara.compile.core-test :refer [observe]]
            [klara.defs :as d] [klara.eval :as ev] [klara.stage :as s]
            [klara.world :as w] [klara.authority :as auth]))

(defn setup [g f]
  (let [world (w/make-world) cache (s/make-cache)]
    (d/define! world (list 'def 'g g))
    (d/define! world (list 'def 'f f))
    (doseq [sym '[g f]] (s/install! cache (cc/compile-def world sym {:inline-fuel 0})))
    [world cache]))

(deftest hot-calls-bypass-cache-and-machine
  (let [[world cache] (setup '(fn [x] (* x 2))
                             '(fn [n] (loop [i n s 0]
                                        (if (> i 0) (recur (dec i) (+ s (g i))) s))))
        f (d/lookup (w/snapshot world) 'f)]
    (s/with-cache cache
      (is (= 110 (f 10)))
      ;; No silent T0 fallback or dynamic cache lookup can pass this check.
      (with-redefs [s/enter (fn [& _] (throw (Exception. "cache entered")))
                    ev/drive (fn [& _] (throw (Exception. "machine constructed")))]
        (dotimes [_ 10] (is (= 110 (f 10))))))
    (testing "slots survive reentering with-cache and invalidate on clear"
      (s/with-cache cache
        (with-redefs [s/enter (fn [& _] (throw (Exception. "slot lost")))]
          (is (= 110 (f 10)))))
      (s/clear! cache)
      (is (= 110 (s/with-cache cache (f 10)))))))

(deftest roots-and-cache-identities
  (let [[world cache] (setup '(fn [x] (+ x 1)) '(fn [x] (* 2 (g x))))
        old (w/fiber world) f (d/lookup (w/basis old) 'f)]
    (is (= 8 (s/with-cache cache (f 3))))
    (d/define! world '(def g (fn [x] (+ x 100))))
    (let [new (w/fiber world)]
      (doseq [sym '[g f]] (s/install! cache (cc/compile-def world sym {:inline-fuel 0})))
      (let [readers (mapv (fn [[fib expected]]
                            (future (s/with-cache cache
                                      (every? #(= expected %) (repeatedly 30 #(d/eval-in fib '(f 3)))))))
                          [[old 8] [new 206] [old 8] [new 206]])]
        (is (every? true? (mapv deref readers))))
      (is (= 8 (s/with-cache cache (f 3))))
      (w/raise-basis! old)
      (is (= 206 (s/with-cache cache (d/eval-in old '(f 3)))))
      (is (= 8 (s/with-cache (s/make-cache) (f 3)))))))

(deftest callee-owns-deopt-and-caller-continues
  (let [[world cache] (setup '(fn [e x probe]
                               (let [seen (count probe) paid (spend! e 1/4) y (* x 2)] (+ y 1)))
                             '(fn [e x probe] (* 3 (g e x probe))))
        trace (atom []) probe (reify clojure.lang.Counted
                                (count [_] (swap! trace conj :seen) 1))
        f (d/lookup (w/snapshot world) 'f)]
    (binding [auth/*store* (auth/new-store)]
      (let [e (auth/op! :auth/evidence [1] [])]
        (is (= 12.0 (s/with-cache cache (f e 1.5 probe))))
        (is (= 3/4 (auth/op! :auth/remaining [e] [])))
        (is (= [:seen] @trace))
        (is (= 1 (:deopts (s/stats cache))))))
    (let [form '(let [e (evidence 1)]
                  (fork [b (f e 1.5 []) c (f e 2 [])] (adopt! b))
                  (remaining e))]
      (is (= (observe world form (s/make-cache)) (observe world form cache))))))

(deftest exceptions-and-handler-context
  (let [[world cache] (setup '(fn [x] (+ 10 (/ 1 x))) '(fn [x] (* 3 (g x))))]
    (doseq [form ['(f 0) '(f) '(f 1 2)
                  '(handle :dynamic {:exn/raise (fn [e k] (k 2))} (f 0))
                  ;; A callback behind a host frame must see the outer handler.
                  '(handle :dynamic {:exn/raise (fn [e k] (k 2))}
                     (first (map f [0])))]]
      (is (= (observe world form (s/make-cache)) (observe world form cache))))
    (is (= [:value 36 ""] (observe world
                           '(handle :dynamic {:exn/raise (fn [e k] (k 2))} (f 0)) cache))))
  (let [[world cache] (setup '(fn [x] (handle [h {:stop (fn [v k] (* v 2))}]
                                       (+ (perform h :stop x) (/ 1 0))))
                             '(fn [x] (+ 1 (g x))))]
    (is (= [:value 9 ""] (observe world '(f 4) cache)))))

(deftest authority-callees-and-generic-fallback
  (let [[world cache] (setup '(fn [e] (do (spend! e 1/4) (remaining e)))
                             '(fn [e] (g e)))]
    (doseq [form ['(let [e (evidence 1)] [(f e) (remaining e)])
                  '(let [e (evidence 1)]
                     (fork [b (f e) c (f e)] (adopt! b)) (remaining e))
                  '(let [e (evidence 1/8)] (f e))]]
      (is (= (observe world form (s/make-cache)) (observe world form cache))))
    ;; Only caller installed: callee falls through the cache to T0.
    (let [caller (first (filter #(= 'f (:name %)) (s/executables cache)))
          other (s/make-cache)]
      (s/install! other caller)
      (is (= [:value 3/4 ""]
             (observe world '(let [e (evidence 1)] (f e)) other))))))

(deftest transitive-effects-and-redefinition-fail-closed
  (let [[world cache] (setup '(fn [x] (+ x 1)) '(fn [x] (* 2 (g x))))]
    (d/define! world '(def h (fn [x] (perform :world/version))))
    (d/define! world '(def g (fn [x] (h x))))
    (is (thrown? clojure.lang.ExceptionInfo (cc/compile-def world 'f {:inline-fuel 0})))
    (let [form '(handle :dynamic {:world/version (fn [k] (+ (k 10) (k 20)))} (f 3))]
      (is (= [:value 60 ""] (observe world form cache)))
      (is (= (observe world form (s/make-cache)) (observe world form cache)))))
  (let [world (w/make-world)]
    (d/define! world '(def f (fn [x] x)))
    (d/define! world '(def g (fn [x] (f x))))
    (d/define! world '(def f (fn [x] (g x))))
    (is (thrown? clojure.lang.ExceptionInfo (cc/compile-def world 'f {:inline-fuel 0})))))


(deftest transitive-read-guards-and-derived-values
  (let [world (w/make-world) cache (s/make-cache)]
    (d/define! world '(def h (fn [x] (+ x 1))))
    (d/define! world '(def g (fn [x] (h x))))
    (d/define! world '(def f (fn [x] (* 2 (g x)))))
    (doseq [sym '[h g f]] (s/install! cache (cc/compile-def world sym {:inline-fuel 0})))
    (s/with-cache cache (d/define! world '(def derived (f 3))))
    (is (some #(= 'h (second %)) (:reads (w/entry* (w/snapshot world) 'derived))))
    (d/define! world '(def h (fn [x] (perform :world/version))))
    (let [form '(handle :dynamic {:world/version (fn [k] (+ (k 10) (k 20)))} (f 3))]
      (is (= [:value 60 ""] (observe world form cache)))
      (is (= (observe world form (s/make-cache)) (observe world form cache))))))

(deftest fallback-keeps-other-cache-contracts-and-callee-arity
  (let [[world _] (setup '(fn [x] (* x 2)) '(fn [x] (g x)))
        cache (s/make-cache) root (w/snapshot world) calls (atom 0)
        g (d/lookup root 'g)]
    (s/install! cache (cc/compile-def world 'f {:inline-fuel 0}))
    (s/install! cache (s/executable g #{[:captures []] [:arg 0 :long]}
                                   (fn [x] (swap! calls inc) (* x 2)) {:test :fallback}))
    (doseq [n [4 4.5 5]]
      (is (= (* n 2) (s/with-cache cache ((d/lookup root 'f) n)))))
    (is (= 2 @calls) "non-ABI executable keeps its runtime argument guard"))
  (let [[world cache] (setup '(fn [x] (* x 2)) '(fn [x] (g x x)))]
    (is (= (observe world '(f 3) (s/make-cache)) (observe world '(f 3) cache)))))

(deftest scalar-entry-carries-context-without-var-pushes
  (let [[world cache] (setup '(fn [x] (* x 2)) '(fn [x] (+ 1 (g x))))
        f (d/lookup (w/snapshot world) 'f)]
    (s/with-cache cache
      (is (= 7 (f 3)))
      (with-redefs [clojure.core/push-thread-bindings
                    (fn [& _] (throw (Exception. "unexpected Var push")))]
        (is (= 9 (f 4)))
        (is (= 11 (f 5)))))
    ;; An ordinary numeric error exits without changing the next entry.
    (is (= (observe world '(f "bad") (s/make-cache))
           (observe world '(f "bad") cache)))
    (is (= 13 (s/with-cache cache (f 6))))))

(deftest recording-is-per-region-and-per-recording-scope
  (let [world (w/make-world) cache (s/make-cache)]
    (d/define! world '(def h (fn [x] (* x 2))))
    (d/define! world '(def g (fn [x] (h x))))
    (d/define! world '(def f (fn [n] (loop [i n s 0]
                                     (if (> i 0) (recur (dec i) (+ s (g i))) s)))))
    (doseq [sym '[h g f]] (s/install! cache (cc/compile-def world sym {:inline-fuel 0})))
    (let [f (d/lookup (w/snapshot world) 'f) reads (atom #{})
          notes (atom []) note w/note-read!]
      (s/with-cache cache
        (f 10)
        (dotimes [_ 2]
          (reset! reads #{})
          (reset! notes [])
          (binding [w/*reads* reads]
            (with-redefs [w/note-read! (fn [r] (swap! notes conj r) (note r))]
              (is (= 110 (f 10)))))
          (is (= '#{g h} (set (map second @reads))))
          (is (= 2 (count @notes)) "transitive reads once, not on each loop call")))
      (s/clear! cache)
      (let [generic (atom #{})]
        (binding [w/*reads* generic] (s/with-cache cache (f 10)))
        (is (= @reads @generic) "R3: same recorded dependency set with cache deleted")))))

(deftest host-protocol-entry-keeps-dynamic-context
  (let [[world cache] (setup '(fn [x] (* x 2)) '(fn [x] (+ 1 (count x))))
        root (w/snapshot world) f (d/lookup root 'f)
        seen (atom [])
        probe (reify clojure.lang.Counted
                (count [_] (swap! seen conj [ev/*basis* ev/*mint*]) 3))]
    (is (false? (:context-only? (first (filter #(= 'f (:name %)) (s/executables cache))))))
    (is (= 4 (s/with-cache cache (f probe))))
    (is (every? #(and (identical? root (first %)) (identical? root (second %))) @seen))
    (is (= 4 (f probe)))))

(deftest twenty-argument-boxed-adapter
  (let [world (w/make-world) cache (s/make-cache)
        ps (mapv #(symbol (str "x" %)) (range 20))]
    (d/define! world (list 'def 'f (list 'fn ps (first ps))))
    (s/install! cache (cc/compile-def world 'f))
    (s/with-cache cache
      (is (= 0 (apply (d/lookup (w/snapshot world) 'f) (range 20)))))))

(deftest explicit-scalar-context-deopt-and-feedback
  (let [[world cache] (setup '(fn [x] (let [y (* x 2)] (+ y 1)))
                             '(fn [x] (* 3 (g x))))
        f (d/lookup (w/snapshot world) 'f)]
    (s/with-cache cache
      (is (= 9 (f 1)))
      (dotimes [_ 5] (is (= 12.0 (f 1.5))))
      (is (= 3 (:deopts (s/stats cache))) "feedback poisons the callee's guard")
      (is (= 15 (f 2))))
    (s/clear! cache)
    (is (= 12.0 (s/with-cache cache (f 1.5))))))

(deftest excessive-arity-declines-before-body
  (let [[world cache] (setup '(fn [x] (* x 2)) '(fn [] 1))
        form (cons 'f (range 21))]
    (is (= (observe world form (s/make-cache)) (observe world form cache)))))

(deftest constant-feedback-key-preserves-every-verdict
  (let [fb (s/make-feedback) site ["code" [:loop []]] key [site :deopt]]
    (dotimes [_ 6]
      (is (= (s/speculate? fb site) (s/speculate-key? fb key)))
      (s/observe! fb site :deopt))))
