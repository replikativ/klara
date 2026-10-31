(ns baseline.run
  "Small shared-fragment diagnostic. Preparation is separate; execution does
   not enable Klara's compiler cache. Run processes sequentially, not as a race."
  (:refer-clojure :exclude [run!])
  (:require [clojure.pprint :as pp] [clojure.java.io :as io]
            [sci.core :as sci] [klara.core :as core] [klara.expand :as expand]
            [klara.eval :as ev] [klara.world :as world])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]))

(def workloads
  {:loop '(fn [n] (loop [i 0 sum 0] (if (< i n) (recur (inc i) (+ sum i)) sum)))
   :calls '(let [f (fn [x] (+ x 1))]
             (fn [n] (loop [i 0 sum 0] (if (< i n) (recur (inc i) (+ sum (f i))) sum))))
   :persistent-update '(fn [n] (loop [i 0 acc [0 0]]
                                (if (< i n)
                                  (recur (inc i) (assoc acc 0 (+ (nth acc 0) i) 1 (inc (nth acc 1)))) acc)))
   :host-callback '(fn [n] (reduce + 0 (map (fn [x] (* x x)) (range n))))})

(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
(defn timed [f]
  (let [t (System/nanoTime) value (f)] {:value value :ns (- (System/nanoTime) t)}))
(defn prepare [engine form]
  (timed #(case engine
            :klara (ev/run (expand/expand-expr form world/empty-root) {:basis world/empty-root})
            :sci (sci/eval-string* (sci/init {}) (pr-str form))
            :clojure (binding [*ns* (the-ns 'baseline.run)] (eval form)))))

(defn measure [f n]
  (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        allocated? (.isThreadAllocatedMemorySupported bean)
        _ (when allocated? (.setThreadAllocatedMemoryEnabled bean true))
        id (.threadId (Thread/currentThread))
        allocated #(if allocated? (.getThreadAllocatedBytes bean id) 0)
        repetitions 10 sink (volatile! nil)
        before (allocated) started (System/nanoTime)]
    (dotimes [_ repetitions] (vreset! sink (f n)))
    {:ns-per-call (/ (- (System/nanoTime) started) (double repetitions))
     :bytes-per-call (when allocated? (/ (- (allocated) before) (double repetitions)))
     :value @sink}))

(defn run! [process]
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
    (let [rows
          (vec (for [[name form] (sort-by key workloads) n [100 1000]]
                 (let [prepared (into {} (for [engine [:clojure :sci :klara]] [engine (prepare engine form)]))
                       expected ((get-in prepared [:clojure :value]) n)]
                   (doseq [[_ {:keys [value]}] prepared]
                     (assert (= expected (value n)))
                     (dotimes [_ 30] (value n)))
                   {:workload name :n n :expected expected
                    :engines (into {} (for [engine [:clojure :sci :klara]
                                          :let [p (get prepared engine)
                                                samples (mapv (fn [_] (measure (:value p) n)) (range 9))]]
                                       (do (assert (every? #(= expected (:value %)) samples))
                                           [engine {:prepare-ns (:ns p)
                                                    :median-ns (median (map :ns-per-call samples))
                                                    :median-bytes (median (map :bytes-per-call samples))
                                                    :samples samples}])))})))
          report {:process process :java (System/getProperty "java.runtime.version")
                  :clojure (clojure-version) :sci "0.15.59" :compiler-cache false
                  :os {:name (System/getProperty "os.name") :arch (System/getProperty "os.arch")
                       :version (System/getProperty "os.version")
                       :available-processors (.availableProcessors (Runtime/getRuntime))}
                  :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
                  :measurement {:warmup-calls 30 :samples 9 :calls-per-sample 10
                                :allocation :current-thread-only}
                  :limits [:shared-fragment :fixed-order :warm-execution :one-machine
                           :no-GC-or-retained-memory-attribution :not-peak-compiled-performance
                           :dependency-loading-excluded-from-preparation]
                  :source-sha256 (into {} (for [p (concat ["deps.edn" "experiments/baseline/run.clj"]
                                                        (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                          [p (core/sha256 (slurp p))]))
                  :rows rows}
          output (str "target/baseline/process-" process ".edn")]
      (io/make-parents output)
      (spit output (with-out-str (pp/pprint report)))
      (println :report output)
      (doseq [row rows]
        (println (:workload row) (:n row)
                 (into {} (map (fn [[engine data]] [engine (select-keys data [:median-ns :median-bytes])])) (:engines row))))
      report)))

(defn -main [& [process]] (run! (or process "0")) (shutdown-agents))
