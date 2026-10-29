(ns klara.compile.unbox-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.compile.core-test :refer [setup observe]]
            [klara.compile.core :as cc] [klara.compile.ir :as ir]
            [klara.defs :as d] [klara.stage :as s]
            [klara.eval :as ev] [klara.world :as w]))

(defn observation [f args cache]
  (try
    (let [v (s/with-cache cache (ev/call-value f args))]
      [:value (class v) (if (instance? Double v) (Double/doubleToRawLongBits v) v)
       (hash v) (= v 1) (get {v :found} v)])
    (catch Throwable e [:error (class e) (.getMessage e)])))

(deftest primitive-loops-preserve-numeric-observations
  (doseq [program ['(fn [n seed] (loop [i n s seed]
                                 (if (> i 0) (recur (dec i) (+ s i)) s)))
                   '(fn [n seed] (loop [i n s seed]
                                 (if (> i 0) (recur (dec i) (* s i)) s)))
                   '(fn [n seed] (loop [i n s seed]
                                 (if (> i 0) (recur (dec i) (- s i)) s)))
                   '(fn [n seed] (loop [i n s seed]
                                 (if (> i 0) (recur (dec i) (/ s i)) s)))]]
    (let [world (setup program) exe (cc/compile-def world 'f)
          f (:value (w/entry* (w/snapshot world) 'f)) cache (s/make-cache)
          args (for [n [0 2 2.5 3/2] seed [0 1 -1 1.5 1/3 Long/MAX_VALUE Long/MIN_VALUE
                                          Double/NaN Double/POSITIVE_INFINITY -0.0
                                          (bigint Long/MAX_VALUE) :bad]] [n seed])]
      (s/install! cache exe)
      (let [expected (mapv #(observation f % (s/make-cache)) args)]
        (is (= expected (mapv #(observation f % cache) args)) (str program))
        (is (pos? (:hits (s/stats cache))))
        (s/clear! cache)
        (is (= expected (mapv #(observation f % cache) args)))))))

(deftest long-and-double-layouts-are-emitted
  (let [world (setup '(fn [n seed] (loop [i n s seed]
                                    (if (> i 0) (recur (dec i) (+ s i)) s))))
        exe (cc/compile-def world 'f) form (pr-str (:form exe))]
    (is (.contains form "clojure.core/long"))
    (is (.contains form "clojure.core/double"))
    (is (not (.contains form "&")))
    (is (= 1 (count (:frame-states exe))))
    (is (nil? (s/check-certificate exe)))
    (is (= :frame-state-mismatch
           (s/check-certificate (assoc-in exe [:frame-states 0 :env 0] [:const 0]))))))

(deftest failed-loop-guard-resumes-current-iteration
  (doseq [changed [1/2 1.5]]
    (let [world (setup '(fn [probe changed]
                         (loop [i 0 s 0]
                           (if (< i 5)
                             (let [seen (count probe)]
                               (recur (inc i) (if (= i 2) changed (+ s i))))
                             s))))
          exe (cc/compile-def world 'f) cache (s/make-cache)
          trace (atom [])
          probe (reify clojure.lang.Counted (count [_] (swap! trace conj :count) 1))
          f (:value (w/entry* (w/snapshot world) 'f))
          expected (observation f [probe changed] (s/make-cache))]
      (is (= 5 (count @trace)))
      (reset! trace [])
      (s/install! cache exe)
      (is (= expected (observation f [probe changed] cache)))
      (is (= [:count :count :count :count :count] @trace))
      (is (= 1 (:deopts (s/stats cache))))
      (s/clear! cache)
      (reset! trace [])
      (is (= expected (observation f [probe changed] cache)))
      (is (= 5 (count @trace))))))

(deftest overflow-keeps-exception-type-and-effect-prefix
  (let [world (setup '(fn [probe seed]
                       (loop [i 2 s seed]
                         (if (> i 0)
                           (let [seen (count probe)] (recur (dec i) (+ s i))) s))))
        f (:value (w/entry* (w/snapshot world) 'f)) cache (s/make-cache)
        trace (atom []) probe (reify clojure.lang.Counted (count [_] (swap! trace conj :count) 0))
        expected (observation f [probe Long/MAX_VALUE] (s/make-cache))]
    (is (= :error (first expected)))
    (is (= ArithmeticException (second expected)))
    (is (= [:count] @trace))
    (reset! trace [])
    (s/install! cache (cc/compile-def world 'f))
    (is (= expected (observation f [probe Long/MAX_VALUE] cache)))
    (is (= [:count] @trace))))

(deftest proven-callee-return-licenses-long-loop
  (let [world (w/make-world)
        _ (d/define! world '(def g (fn [x] (* x 2))))
        _ (d/define! world '(def f (fn [n]
                                     (loop [i n s 0]
                                       (if (> i 0) (recur (dec i) (+ s (g i))) s)))))
        old (w/snapshot world)
        g-exe (cc/compile-def world 'g {:inline-fuel 0})
        f-exe (cc/compile-def world 'f {:inline-fuel 0})
        f (d/lookup old 'f) cache (s/make-cache)]
    (is (= {:args [:long] :return :long} (:return-layout g-exe)))
    (is (.contains (pr-str (:form f-exe)) "clojure.core/long"))
    (s/install! cache g-exe)
    (s/install! cache f-exe)
    (doseq [n [0 1 20 200 2.5 :bad]]
      (is (= (observation f [n] (s/make-cache))
             (observation f [n] cache)) (str n)))
    (d/define! world '(def g (fn [x] (/ x 2))))
    (is (= (observation f [20] (s/make-cache))
           (observation f [20] cache)))
    (is (= 420 (s/with-cache cache (ev/call-value f [20]))))))

(deftest mixed-callee-return-does-not-license-layout
  (let [world (w/make-world)
        _ (d/define! world '(def g (fn [x] (if (> x 0) x 1.5))))
        _ (d/define! world '(def f (fn [n]
                                     (loop [i n s 0]
                                       (if (> i 0) (recur (dec i) (+ s (g i))) s)))))
        g-exe (cc/compile-def world 'g {:inline-fuel 0})]
    (is (nil? (:return-layout g-exe)))))
