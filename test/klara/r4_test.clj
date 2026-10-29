(ns klara.r4-test
  "Gate R4: old and new versions of a macro and of a function coexist
  across forks and pinned fibers, concurrently. Includes X1's measured
  leak (a parent g calling f saw the fork's f through the shared host
  namespace), which basis-specific execution must fix."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.world :as w]
            [klara.defs :as d]))

(deftest x1-leak-is-fixed
  (let [wo (w/make-world)]
    (d/define! wo '(def f (fn [x] (+ x 1))))
    (d/define! wo '(def g (fn [x] (f x))))
    (let [fk (w/fork wo)]
      (d/define! fk '(def f (fn [x] (* x 10))))
      (is (= 30 ((d/lookup (w/snapshot fk) 'g) 3)) "the fork's g sees the fork's f")
      (is (= 4 ((d/lookup (w/snapshot wo) 'g) 3)) "the parent's g does NOT (X1 measured 30)")
      (is (identical? (:value (w/entry* (w/snapshot wo) 'g))
                      (:value (w/entry* (w/snapshot fk) 'g)))
          "one and the same g value, executed under two bases"))))

(defn- base-world []
  (let [wo (w/make-world)]
    (doseq [df '[(defmacro twice [e] (qq (+ ~e ~e)))
                 (def f (fn [y] (twice y)))
                 (def scale (fn [x] x))
                 (def g (fn [y] (scale (f y))))]]
      (d/define! wo df))
    wo))

(defn- edit! [wo macro-body scale-body]
  (d/define! wo (list 'defmacro 'twice '[e] macro-body))
  (d/invalidate! wo 'twice)
  (d/define! wo (list 'def 'scale (list 'fn '[x] scale-body))))

(deftest r4-concurrent-versions
  (let [wo (base-world)
        fk (w/fork wo)
        p-old (w/fiber wo)
        q-old (w/fiber fk)
        _ (edit! wo '(qq (* ~e ~e)) '(* 10 x))
        _ (edit! fk '(qq (- ~e 1)) '(+ 100 x))
        p-new (w/fiber wo)
        q-new (w/fiber fk)
        expect {p-old 6, p-new 90, q-old 6, q-new 102}
        stop (atom false)
        writer (future
                 (loop [i 0]
                   (when-not @stop
                     (d/define! wo (list 'def (symbol (str "noise" (mod i 7))) i))
                     (d/define! fk (list 'def (symbol (str "noise" (mod i 5))) i))
                     (recur (inc i))))
                 :done)
        readers (mapv (fn [[fib v]]
                        (future
                          (vec (for [_ (range 200)]
                                 [(= v (d/eval-in fib '(g 3)))
                                  (= v ((d/lookup (w/basis fib) 'g) 3))]))))
                      expect)
        observed (mapv deref readers)]
    (reset! stop true)
    (is (= :done @writer))
    (is (every? #(every? (partial = [true true]) %) observed)
        "every pinned fiber saw exactly its version on every read")
    (testing "the macro versions differ per basis"
      (is (= [6 9 6 2] (mapv #(d/eval-in % '(f 3)) [p-old p-new q-old q-new]))))
    (testing "raising moves a fiber to its world's newest version"
      (w/raise-basis! p-old)
      (w/raise-basis! q-old)
      (is (= [90 102] [(d/eval-in p-old '(g 3)) (d/eval-in q-old '(g 3))])))
    (testing "the fork still pins the parent's original root"
      (is (= 6 ((d/lookup (:parent fk) 'g) 3))))))
