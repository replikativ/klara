(ns klara.compile-bench
  "End-to-end and warmed ABI benchmarks. Run experiments/compiler/run.sh;
  it compiles independent Java baselines before starting the capped JVM."
  (:refer-clojure :exclude [run!])
  (:require [klara.compile.core :as compiler] [klara.defs :as d]
            [klara.eval :as ev] [klara.world :as w] [klara.stage :as stage])
  (:import [klara.bench Baselines]))

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

(def call-program
  '(fn [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s (g i))) s))))
(def programs (assoc programs :calls call-program))
(defn clojure-g [x] (* x 2))
(def clojure-functions
  (assoc clojure-functions :calls
         (fn [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s (clojure-g i))) s)))))
(def java-functions
  {:numeric #(Baselines/numeric (long %))
   :collections #(Baselines/collections (long %))
   :closures #(Baselines/closures (long %))
   :tail-effects #(Baselines/tailEffects (long %))
   :calls #(Baselines/calls (long %))})

(def java-source-functions
  {:numeric (:numeric java-functions) :calls (:calls java-functions)
   :collections #(Baselines/sourceCollections (long %))
   :closures #(Baselines/sourceClosures (long %))
   :tail-effects #(Baselines/sourceTailEffects (long %))})

(def programs
  (assoc programs
         :hof-pipeline '(fn [n] (reduce (fn [a x] (+ a x)) 0
                                       (filter (fn [x] (even? x))
                                               (map (fn [x] (+ x 1)) (range n)))))
         :hof-mapv '(fn [n] (reduce (fn [a x] (+ a x)) 0
                                   (mapv (fn [x] (* x 2)) (vec (range n)))))))
(def clojure-functions
  (assoc clojure-functions
         :hof-pipeline (fn [n] (reduce (fn [a x] (+ a x)) 0
                                      (filter (fn [x] (even? x))
                                              (map (fn [x] (+ x 1)) (range n)))))
         :hof-mapv (fn [n] (reduce (fn [a x] (+ a x)) 0
                                  (mapv (fn [x] (* x 2)) (vec (range n)))))))
(def java-functions
  (assoc java-functions :hof-pipeline #(Baselines/hofPipeline (long %))
                        :hof-mapv #(Baselines/hofMapv (long %))))
(def java-source-functions
  (merge java-source-functions (select-keys java-functions [:hof-pipeline :hof-mapv])))

(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
(def sink (volatile! nil))

(defn timed [f n]
  (let [start (System/nanoTime)]
    (dotimes [_ n] (vreset! sink (f)))
    (/ (- (System/nanoTime) start) 1e6 n)))
(defn measure [f]
  (dotimes [_ 100] (f))
  (median (repeatedly 7 #(timed f 20))))

(defn run! []
  (println {:java (System/getProperty "java.version") :clojure (clojure-version)
            :input 200 :warmup 100 :batches 7 :calls-per-batch 20})
  (doseq [[label program] (sort-by key programs)]
    (let [world (w/make-world) _ (d/define! world '(def g (fn [x] (* x 2))))
          _ (d/define! world (list 'def 'f program))
          f (d/lookup (w/snapshot world) 'f) cache (stage/make-cache)
          opts (if (= label :calls) {:inline-fuel 0} {})
          _ (when (= label :calls) (stage/install! cache (compiler/compile-def world 'g opts)))
          compilations (repeatedly 5 #(compiler/compile-def world 'f opts))
          exes (vec compilations) exe (last exes)
          _ (stage/install! cache exe)
          generic #(binding [ev/*entry-hook* nil ev/*direct-hook* nil] (ev/call-value f [200]))
          compiled #(stage/with-cache cache (ev/call-value f [200]))
          plain #((clojure-functions label) 200) java #((java-functions label) 200)
          expected (generic)]
      (assert (= expected (compiled) (plain) (java) ((java-source-functions label) 200)))
      (let [t0 (measure generic) t1 (measure compiled) host (measure plain) j (measure java)]
        (println {:benchmark label :result expected :T0-ms t0 :compiled-ms t1
                  :T0/compiled (/ t0 t1) :clojure-ms host :compiled/clojure (/ t1 host)
                  :java-ms j :compiled/java (/ t1 j)
                  :compile-ms (median (map :compile-ms exes))
                  :allocations-removed (:allocations-removed exe)})))))


(defn steady!
  "Long warmup within a persistent cache scope; all paths include result
  boxing and the Clojure measurement driver. Do not time T0 100,000 times."
  []
  (println {:mode :steady :warmup 10000 :batches 9 :calls-per-batch 10000})
  (doseq [n [200 2000] [label program] (sort-by key programs)]
    (let [world (w/make-world) cache (stage/make-cache)
          _ (d/define! world '(def g (fn [x] (* x 2))))
          _ (d/define! world (list 'def 'f program))
          f (d/lookup (w/snapshot world) 'f)
          opts (if (= label :calls) {:inline-fuel 0} {})
          _ (when (= label :calls) (stage/install! cache (compiler/compile-def world 'g opts)))
          exe (compiler/compile-def world 'f opts)
          _ (stage/install! cache exe)
          plain (clojure-functions label) java (java-functions label)
          sample (fn [call]
                   (dotimes [_ 10000] (call))
                   (median (repeatedly 9 #(timed call 10000))))]
      (stage/with-cache cache
        (assert (= (f n) (plain n) (java n) ((java-source-functions label) n)))
        (let [t (sample #(f n)) c (sample #(plain n)) j (sample #(java n))
              body (when (= :numeric label) (sample #((:run exe) n)))]
          (println {:benchmark label :input n :compiled-ms t :clojure-ms c :java-ms j
                    :compiled/clojure (/ t c) :compiled/java (/ t j)
                    :numeric-body-ms body :entry-stats (stage/stats cache)}))))))
