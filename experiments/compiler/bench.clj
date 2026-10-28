(ns klara.compile-bench
  "S9 end-to-end cache-entry benchmarks against T0 and plain Clojure. Run with
  clojure -M -e '(load-file \"experiments/compiler/bench.clj\") (klara.compile-bench/run!)'.
  Seven batches of twenty calls after one hundred warmup calls; medians
  are milliseconds per call. Compilation median is five compilations."
  (:refer-clojure :exclude [run!])
  (:require [klara.compile.core :as compiler] [klara.defs :as d]
            [klara.eval :as ev] [klara.world :as w] [klara.stage :as stage]))

(def programs
  {:numeric '(fn [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s i)) s)))
   :collections '(fn [n] (loop [i n s 0]
                           (if (> i 0)
                             (let [v [i (+ i 1)] m {:a (first v) :b (second v)}]
                               (recur (dec i) (+ s (get m :a) (get m :b)))) s)))
   :closures '(fn [n] (loop [i n s 0]
                        (if (> i 0) (let [f (fn [x] (+ x i))]
                                      (recur (dec i) (+ s (f 1) (f 2)))) s)))
   :tail-effects '(fn [n] (handle [h {:weight (fn [x k] (k (* x 2)))}]
                           (loop [i n s 0]
                             (if (> i 0) (recur (dec i) (+ s (perform h :weight i))) s))))})

(def clojure-functions
  ;; Written independently of the compiler. Use ordinary Clojure locals,
  ;; collections and calls, with the lexical :weight clause as a local fn.
  {:numeric (fn [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s i)) s)))
   :collections (fn [n] (loop [i n s 0]
                         (if (> i 0)
                           (let [v [i (+ i 1)] m {:a (first v) :b (second v)}]
                             (recur (dec i) (+ s (get m :a) (get m :b)))) s)))
   :closures (fn [n] (loop [i n s 0]
                      (if (> i 0) (let [f (fn [x] (+ x i))]
                                    (recur (dec i) (+ s (f 1) (f 2)))) s)))
   :tail-effects (fn [n] (let [weight (fn [x] (* x 2))]
                           (loop [i n s 0]
                             (if (> i 0) (recur (dec i) (+ s (weight i))) s))))})

(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
(defn timed [f n]
  (let [start (System/nanoTime)]
    (dotimes [_ n] (f))
    (/ (- (System/nanoTime) start) 1e6 n)))
(defn measure [f]
  (dotimes [_ 100] (f))
  (median (repeatedly 7 #(timed f 20))))

(defn run! []
  (println {:java (System/getProperty "java.version") :clojure (clojure-version)
            :input 200 :warmup 100 :batches 7 :calls-per-batch 20})
  (doseq [[label program] (sort-by key programs)]
    (let [world (w/make-world) _ (d/define! world (list 'def 'f program))
          f (:value (w/entry* (w/snapshot world) 'f)) cache (stage/make-cache)
          compilations (repeatedly 5 #(compiler/compile-def world 'f {}))
          exes (vec compilations) exe (last exes)
          _ (stage/install! cache exe)
          generic #(binding [ev/*entry-hook* nil] (ev/call-value f [200]))
          compiled #(stage/with-cache cache (ev/call-value f [200]))
          plain #((clojure-functions label) 200)
          expected (generic)]
      (assert (= expected (compiled) (plain)))
      (let [t0 (measure generic) t1 (measure compiled) host (measure plain)]
        (println {:benchmark label :result expected :T0-ms t0 :compiled-ms t1
                  :T0/compiled (/ t0 t1) :clojure-ms host :compiled/clojure (/ t1 host)
                  :compile-ms (median (map :compile-ms exes))
                  :allocations-removed (:allocations-removed exe)})))))
