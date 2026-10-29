(ns klara.compile.speculate-test
  (:require [clojure.test :refer [deftest is]]
            [klara.compile.core-test :refer [setup observe]]
            [klara.compile.core :as cc] [klara.stage :as s]))

(deftest generated-frames-reconstruct-virtual-objects
  (let [world (setup '(fn [n probe]
                       (let [seen (count probe)
                             v [n seen]
                             f (fn [x] (+ x seen))]
                         (+ n (f (second v))))))
        cache (s/make-cache) exe (cc/compile-def world 'f)
        trace (atom [])
        probe (reify clojure.lang.Counted (count [_] (swap! trace conj :count) 2))
        form (list 'f 1.5 (list 'quote probe))]
    (is (= 1 (count (:frame-states exe))))
    (is (some #(= :closure (first %)) (get-in exe [:frame-states 0 :env])))
    (is (some #(= :vector (first %)) (get-in exe [:frame-states 0 :env])))
    (is (= 2 (:allocations-removed exe)))
    ;; T0 actually calls the rebuilt closure and projects the rebuilt vector.
    (s/install! cache exe)
    (is (= [:value 5.5 ""] (observe world form cache)))
    (is (= [:count] @trace))
    (is (= 1 (:deopts (s/stats cache))))
    (reset! trace [])
    (s/clear! cache)
    (is (= [:value 5.5 ""] (observe world form cache)))
    (is (= [:count] @trace)))
  (let [world (setup '(fn [n] (let [v [n 2] f (fn [x] (+ x 1)) y (f (first v))] (+ y 1))))
        exe (cc/compile-def world 'f) cache (s/make-cache)]
    (is (= 2 (:allocations-removed exe)))
    (s/install! cache exe)
    (doseq [n [1 1.5 :bad Long/MAX_VALUE]]
      (let [form (list 'f n)]
        (is (= (observe world form (s/make-cache)) (observe world form cache)))))))

(deftest authority-is-live-and-never-replayed
  (let [world (setup '(fn [e n] (let [paid (spend! e 1/4) y n] (+ y 1))))
        exe (cc/compile-def world 'f) cache (s/make-cache)
        form '(let [e (evidence 1)] [(f e 1.5) (remaining e)])]
    (s/install! cache exe)
    (is (= [:value [2.5 3/4] ""] (observe world form cache)))
    (is (= 1 (:deopts (s/stats cache))))
    (is (= (observe world form (s/make-cache)) (observe world form cache)))
    (let [forked '(let [e (evidence 1)]
                    (fork [b (f e 1.5)] (adopt! b)) (remaining e))]
      (is (= (observe world forked (s/make-cache)) (observe world forked cache))))))

(deftest poisoned-site-stops-deoptimizing
  (let [world (setup '(fn [n] (let [y (* n 2)] (+ y 1))))
        exe (cc/compile-def world 'f) cache (s/make-cache)]
    (s/install! cache exe)
    (dotimes [_ 7] (is (= [:value 4.0 ""] (observe world '(f 1.5) cache))))
    (is (= 3 (:deopts (s/stats cache))))
    (is (false? (s/speculate? (s/cache-feedback cache)
                            [(:code-id exe) (get-in exe [:frame-states 0 :site])])))))

(deftest install-binds-generated-frames-to-certificate
  (let [exe (cc/compile-def (setup '(fn [n] (let [y (* n 2)] (+ y 1)))) 'f)]
    (is (= :frame-state-mismatch
           (s/check-certificate (assoc-in exe [:frame-states 0 :env 0] [:const 0]))))))

(deftest authorities-inside-virtual-objects
  (let [world (setup '(fn [e n]
                       (let [paid (spend! e 1/4) v [e]
                             f (fn [x] (+ x (remaining e)))]
                         (+ n (f (remaining (first v)))))))
        exe (cc/compile-def world 'f) cache (s/make-cache)
        form '(let [e (evidence 1)] [(f e 1.5) (remaining e)])]
    (is (= 2 (:allocations-removed exe)))
    (s/install! cache exe)
    (is (= [:value [3.0 3/4] ""] (observe world form cache)))
    (is (= 1 (:deopts (s/stats cache))))
    (is (= (observe world form (s/make-cache)) (observe world form cache)))))

(deftest unsupported-checkpoints-keep-ordinary-compilation
  (doseq [program ['(fn [n] (let [m {:a n} y (get m :a)] (+ y 1)))
                   '(fn [n] (let [v #{n} y (count v)] (+ y 1)))
                   '(fn [n] (let [y n] (if (> y 0) (+ y 1) (+ y 2))))
                   '(fn [n] (handle [h {:op (fn [x k] (k x))}]
                              (let [y (perform h :op n)] (+ y 1))))]]
    (let [world (setup program) exe (cc/compile-def world 'f) cache (s/make-cache)]
      (is (nil? (:frame-states exe)))
      (s/install! cache exe)
      (is (= (observe world '(f 3) (s/make-cache)) (observe world '(f 3) cache))))))
