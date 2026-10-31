(ns interpreter.mutable-checks
  (:require [clojure.test :refer [deftest is]] [interpreter.mutable :as m]
            [klara.eval :as ev] [klara.expand :as x] [klara.world :as w]
            [klara.core :as core]))

(def programs
  ['(fn [n] (loop [i 0 s 0] (if (< i n) (recur (inc i) (+ s i)) s)))
   '(fn [n] (letfn [(fib [x] (if (< x 2) x (+ (fib (- x 1)) (fib (- x 2)))))] (fib n)))
   '(fn [n] (let [make (fn [x] (fn [y] (+ x y))) f (make n)] (f 4)))
   '(fn [n] (let [f (fn [x] (+ x n)) g (fn [h x] (h (h x)))] (g f 3)))
   '(fn [n] (+ 1 (loop [i 0 s 0] (if (< i n) (recur (inc i) (+ s i)) s))))
   '(fn [n] (loop [i 0 v [0 0]]
              (if (< i n) (recur (inc i) (assoc v 0 (+ (nth v 0) i) 1 (inc (nth v 1)))) v)))
   '(fn [n] (letfn [(even [x] (if (zero? x) true (odd (dec x))))
                    (odd [x] (if (zero? x) false (even (dec x))))] (even n)))])

(deftest pure-programs-and-snapshots-match-both-t0-drivers
  (doseq [form programs n [0 1 4 8]
          :let [term (x/expand-expr form w/empty-root) f (m/prepare term)
                expected (binding [ev/*reference-driver* true] ((ev/run term) n))]]
    (is (= expected ((ev/run term) n) (m/invoke f n)))
    ;; Pause inside argument evaluation, pending calls, recursion, array growth
    ;; and completed states. Every thaw has private active registers/frames.
    (doseq [fuel [0 1 2 7 23 101]]
      (let [state (m/start f [n]) _ (m/advance! state fuel)
            frozen (m/freeze state)
            a (m/thaw frozen) b (m/thaw frozen)]
        (m/advance! a 3)
        (is (= expected (m/run! state) (m/run! b) (m/run! a)
               (m/run! (m/thaw frozen))))))))

(deftest larger-environments-closures-and-repeated-pauses
  (let [bindings (vec (mapcat (fn [i] [(symbol (str "v" i)) i]) (range 40)))
        form (list 'fn '[n] (list 'let bindings (list '+ 'v0 'v39 'n)))
        term (x/expand-expr form w/empty-root) f (m/prepare term)
        state (m/start f [5])]
    (dotimes [_ 150] (m/advance! state 1))
    (is (= 44 (m/run! state) (m/run! (m/thaw (m/freeze state)))))))

(deftest unsupported-effects-mutation-and-escaping-values-decline
  (doseq [form ['(fn [x] (println x)) '(fn [x] (code x))
                '(fn [x] (handle [h {:op (fn [k] (k x))}] (perform h :op)))
                '(fn [& xs] xs)]]
    (is (thrown? clojure.lang.ExceptionInfo (m/prepare (x/expand-expr form w/empty-root)))))
  (let [f (m/prepare (x/expand-expr '(fn [x] x) w/empty-root))]
    (is (thrown? clojure.lang.ExceptionInfo (m/invoke f (atom 0))))
    (is (thrown? clojure.lang.ExceptionInfo (m/invoke f [(atom 0)]))))
  (let [f (m/prepare (x/expand-expr '(fn [x] (fn [] x)) w/empty-root))]
    (is (thrown? clojure.lang.ExceptionInfo (m/invoke f 1))))
  (let [f (m/prepare (x/expand-expr '(fn [x] (+ x 1)) w/empty-root)) called (atom false)]
    (with-redefs [core/prims (assoc core/prims '+ (fn [& _] (reset! called true)))]
      (is (thrown? clojure.lang.ExceptionInfo (m/invoke f 1)))
      (is (false? @called))))
  (let [f (m/prepare (x/expand-expr '(fn [x] (+ x 1)) w/empty-root))]
    (is (thrown? ArithmeticException (m/invoke f Long/MAX_VALUE)))
    (is (thrown? clojure.lang.ExceptionInfo (m/advance! (m/start f [1]) -1)))))
