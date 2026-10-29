(ns klara.compile.hof-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.core-test :refer [setup observe]]
            [klara.compile.core :as cc] [klara.compile.generated-test :as generated]
            [klara.defs :as d] [klara.eval :as ev] [klara.stage :as stage]
            [klara.world :as w]))

(defn compare! [program inputs]
  (let [world (setup program) cache (stage/make-cache)
        exe (cc/compile-def world 'f) trace (atom []) probe (generated/probes trace)]
    (stage/install! cache exe)
    (doseq [input inputs]
      (let [call (list 'f (list 'quote input) (list 'quote probe))]
        (is (= (generated/observations world call (stage/make-cache) trace)
               (generated/observations world call cache trace)) (pr-str [program input]))))
    (is (pos? (:hits (stage/stats cache))))
    exe))

(deftest eager-hofs-and-direct-vector-loops
  (doseq [body ['(mapv (fn [x] (+ x 1)) xs)
                '(let [f (fn [x] (+ x 1)) alias f] (mapv alias xs))
                '(reduce (fn [a x] (+ a x)) 0 xs)
                '(some (fn [x] (if (> x 1) x false)) xs)
                '(every? (fn [x] (< x 3)) xs)
                '(into [] (filter (fn [x] (> x 0)) (map (fn [x] (+ x 1)) xs)))
                '(vec (map (fn [x] (+ x 1)) xs))
                '(reduce + 0 (filter (fn [x] (pos? x)) (map (fn [x] (+ x 1)) xs)))
                '(mapv (fn [x] (* x 2)) [1 (count (first probe)) 3])
                '(reduce (fn [a x] (+ a x)) 0 [1 (count (first probe)) 3])
                '(reduce (fn [a x] (if (> x 2) (reduced a) (+ a x))) 0 xs)]]
    (testing (pr-str body)
      (compare! (list 'fn ['xs 'probe] body)
                [nil [] [1] [0 1 2 3] '(1 2 3) (range 70) [1.5 2/3] [Long/MAX_VALUE 1] [:bad]]))))

(deftest chunking-effects-exceptions-and-short-circuit
  ;; Counted elements reveal the entire observable callback schedule, including
  ;; map chunk run-ahead before a filter, reducer or short circuit consumer.
  (let [trace (atom [])
        xs (mapv (fn [i] (reify clojure.lang.Counted
                           (count [_] (swap! trace conj i) i))) (range 70))]
    (doseq [body ['(reduce (fn [a x] (do (count (second probe)) (+ a x))) 0
                          (filter (fn [x] (do (count (first probe)) (even? x)))
                                  (map (fn [x] (count x)) xs)))
                  '(some (fn [x] (> x 1)) (map (fn [x] (count x)) xs))
                  '(every? (fn [x] (< x 1)) (map (fn [x] (count x)) xs))
                  '(vec (map (fn [x] (/ 1 (count x))) xs))]]
      (let [world (setup (list 'fn ['xs 'probe] body)) cache (stage/make-cache)
            probe (generated/probes trace) call (list 'f (list 'quote xs) (list 'quote probe))]
        (stage/install! cache (cc/compile-def world 'f))
        (is (= (generated/observations world call (stage/make-cache) trace)
               (generated/observations world call cache trace)))))))

(deftest authorities-and-admission
  (let [world (setup '(fn [e] (reduce (fn [a x] (do (spend! e 1/4) (+ a x))) 0 [1 2])))
        cache (stage/make-cache)]
    (stage/install! cache (cc/compile-def world 'f))
    (doseq [call ['(let [e (evidence 1)] [(f e) (remaining e)])
                  '(let [e (evidence 1/4)] (f e))
                  '(let [e (evidence 1)] (fork [a (f e) b (f e)] (adopt! a)) (remaining e))
                  '(handle :dynamic {:host/call (fn [sym f init xs k] (k 99))}
                           (let [e (evidence 1)] (f e)))
                  '(handle :dynamic {:exn/raise (fn [x k] (k 10))}
                           (let [e (evidence 1/4)] (f e)))]]
      (is (= (observe world call (stage/make-cache)) (observe world call cache))))))

(deftest guarded-world-callback-and-cache-deletion
  (let [world (w/make-world) cache (stage/make-cache)]
    (d/define! world '(def helper (fn [x] (+ x 1))))
    (d/define! world '(def f (fn [xs] (mapv helper xs))))
    (stage/install! cache (cc/compile-def world 'f))
    (let [old (w/fork world)]
      (d/define! world '(def helper (fn [x] (+ x 100))))
      (doseq [world [world old]]
        (is (= (observe world '(f [1 2]) (stage/make-cache))
               (observe world '(f [1 2]) cache)))))
    (stage/clear! cache)
    (is (= [:value [101 102] ""] (observe world '(f [1 2]) cache)))))

(deftest no-callback-t0-machine
  (let [world (setup '(fn [xs] (reduce (fn [a x] (+ a x)) 0
                                      (map (fn [x] (* x 2)) xs))))
        exe (cc/compile-def world 'f)]
    (with-redefs [ev/drive (fn [& _] (throw (ex-info "unexpected T0" {})))]
      (is (= 12 ((:run exe) [1 2 3]))))))

(deftest unsupported-callbacks-decline
  (doseq [p ['(fn [xs] (map (fn [x] (+ x 1)) xs))
             '(fn [xs] (let [ys (map (fn [x] (+ x 1)) xs)] (vec ys)))
             '(fn [xs] (mapv (fn [x] (fn [] x)) xs))
             '(fn [xs] (mapv (fn [x] (println x)) xs))
             '(fn [xs] (mapv (fn [x y] (+ x y)) xs))
             '(fn [xs] (reduce (fn [a x] (+ a x)) xs))
             '(fn [xs] (handle [h {:op (fn [x k] (k x))}]
                               (mapv (fn [x] (perform h :op x)) xs)))
             '(fn [xs] (into [] (map (fn [x] x))))]]
    (is (thrown? clojure.lang.ExceptionInfo (cc/compile-def (setup p) 'f)) (pr-str p))))

(deftest reducible-input-keeps-host-protocol
  (let [xs (reify clojure.lang.IReduceInit
             (reduce [_ f init] (f (f init 10) 20)))]
    (let [world (setup '(fn [xs] (reduce (fn [a x] (+ a x)) 1 xs)))
          cache (stage/make-cache) call (list 'f (list 'quote xs))]
      (stage/install! cache (cc/compile-def world 'f))
      (is (= (observe world call (stage/make-cache)) (observe world call cache)))
      (is (pos? (:fallbacks (stage/stats cache)))))))

(deftest host-root-rebinding-and-transitive-admission
  (let [world (w/make-world) cache (stage/make-cache)]
    (d/define! world '(def g (fn [xs] (mapv (fn [x] (+ x 1)) xs))))
    (d/define! world '(def f (fn [xs] (g xs))))
    (doseq [s '[g f]] (stage/install! cache (cc/compile-def world s {:inline-fuel 0})))
    ;; Warm direct slots first. A changed host root must be checked on hits.
    (is (= [:value [2 3] ""] (observe world '(f [1 2]) cache)))
    (with-redefs [clojure.core/mapv (fn [& _] :overridden)]
      ;; observe/expand themselves use mapv, so invoke the retained closure.
      (let [f (d/lookup (w/snapshot world) 'f)]
        (is (= :overridden (stage/with-cache cache (f [1 2]))))))))


(deftest custom-reducer-cannot-retain-emitted-callback
  (let [world (setup '(fn [xs] (reduce (fn [a x] (+ a x)) 0 xs)))
        cache (stage/make-cache) retained (atom nil)
        xs (reify clojure.lang.IReduceInit (reduce [_ f _] (reset! retained f) 42))
        call (list 'f (list 'quote xs))]
    (stage/install! cache (cc/compile-def world 'f))
    (is (= [:value 42 ""] (observe world call cache)))
    (is (ev/closure? @retained))
    (is (pos? (:fallbacks (stage/stats cache))))))
