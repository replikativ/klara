(ns adaptive-affine.bench
  "Single-process diagnostics. Load this file into a persistent REPL."
  (:refer-clojure :exclude [run! bean])
  (:require [clojure.java.io :as io]
            [clojure.pprint :as pp]
            [klara.authority :as a]
            [klara.compile.affine-erase :as erase]
            [klara.compile.infer-affine :as ia]
            [klara.compile.staged :as staged]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w]))

(defn load-world []
  (let [world (w/make-world)]
    (with-open [r (java.io.PushbackReader. (io/reader "examples/staging/08-inferred-affine.klr"))]
      (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} r)))]
        (d/define! world form))) world))

(defn functional [^long n ^long split]
  (loop [i (long 0) acc [0 0]]
    (if (< i n)
      (if (< i split)
        (recur (inc i) (assoc acc 0 (inc (nth acc 0))))
        (recur (inc i) (assoc acc 1 (inc (nth acc 1))))) acc)))

(defn transient-counter [^long n ^long split]
  (loop [i (long 0) acc (transient [0 0])]
    (if (< i n)
      (if (< i split)
        (recur (inc i) (assoc! acc 0 (inc (nth acc 0))))
        (recur (inc i) (assoc! acc 1 (inc (nth acc 1))))) (persistent! acc))))

(defn handwritten [^long n ^long split]
  (let [buffer (long-array [0 0])]
    (loop [i (long 0)]
      (when (< i n)
        (if (< i split)
          (aset buffer 0 (inc (aget buffer 0)))
          (aset buffer 1 (inc (aget buffer 1))))
        (recur (inc i))))
    (vec buffer)))

(def ^com.sun.management.ThreadMXBean bean
  (java.lang.management.ManagementFactory/getThreadMXBean))
(defn allocated [] (.getThreadAllocatedBytes bean (.threadId (Thread/currentThread))))
(defn cpu [] (.getCurrentThreadCpuTime bean))
(defn median [xs] (nth (sort xs) (quot (count xs) 2)))
(defn measure [iterations batches f]
  (let [sink (volatile! nil)
        samples (vec (repeatedly batches
                       #(let [bytes (allocated) start (System/nanoTime)]
                          (dotimes [_ iterations] (vreset! sink (f)))
                          {:ns (/ (- (System/nanoTime) start) (double iterations))
                           :bytes (/ (- (allocated) bytes) (double iterations))})))]
    {:median-ns (median (map :ns samples)) :median-bytes (median (map :bytes samples))
     :samples samples :value @sink}))

(defn run! []
  (let [start (System/nanoTime) world (load-world) root (w/snapshot world)
        generation-ns (- (System/nanoTime) start)
        source (d/lookup root 'counter-code) f (d/lookup root 'counter)
        cache (stage/make-cache) candidate (ia/prepare root source)
        info (staged/prepared-info candidate) inferred (:inference info)
        boxed (eval (:form (erase/erase (:owned inferred) (:derivation inferred) {:in-place? false})))
        primitive (eval (:form info))
        start (System/nanoTime) _ (staged/install! cache root candidate)
        install-ns (- (System/nanoTime) start)
        functions {:clojure-functional functional :clojure-transient transient-counter
                   :handwritten-array handwritten :erased-boxed boxed :erased-array primitive
                   :guarded #(stage/with-cache cache (ev/call-value f [%1 %2]))
                   :t0 #(binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
                          (ev/call-value f [%1 %2]))}
        sizes [32 256 1024 4096]
        _ (doseq [n sizes [label fun] functions]
            (dotimes [_ (if (= label :t0) 20 3000)] (fun n (quot n 3))))
        rows (mapv (fn [n]
                     (let [samples (into {} (for [[label fun] functions]
                                             [label (measure (if (= label :t0) 8 300) 7 #(fun n (quot n 3)))]))]
                       (assert (apply = (map :value (vals samples))))
                       {:n n :measurements samples})) sizes)
        ;; Exact example policy overhead, including T0 collection traversal,
        ;; profiling effect, returned controller and retained result vector.
        batch-size 24 inputs (vec (repeat batch-size [256 80]))
        controller (d/eval-form root '(counter-controller counter-code 0))
        policy (fn [] (stage/with-cache cache
                        (ev/call-value (d/lookup root 'operate-counter) [controller inputs 2])))
        plain (fn [] (stage/with-cache cache (mapv #(ev/call-value f %) inputs)))
        _ (dotimes [_ 100] (policy) (plain))
        profile (measure 10 7 policy) plain-batch (measure 10 7 plain)
        per-call-overhead (/ (- (:median-ns profile) (:median-ns plain-batch)) batch-size)
        setup-ns (+ generation-ns (* 1e6 (:compile-ms info)) install-ns)
        result {:java (System/getProperty "java.runtime.version")
                :generation-and-definitions-ns generation-ns :compile-ns (* 1e6 (:compile-ms info))
                :install-ns install-ns
                :controller {:batch-size batch-size :profiled (dissoc profile :value)
                             :plain (dissoc plain-batch :value) :extra-ns-per-call per-call-overhead}
                :rows (mapv (fn [{:keys [measurements] :as row}]
                              (assoc row :break-even-calls
                                     (into {} (for [baseline [:t0 :clojure-functional]]
                                                (let [saving (- (get-in measurements [baseline :median-ns])
                                                                (get-in measurements [:guarded :median-ns])
                                                                per-call-overhead)]
                                                  [baseline (when (pos? saving)
                                                              (long (Math/ceil (/ setup-ns saving))))]))))) rows)
                :limitations [:single-process :fixed-order :already-warm-jvm
                              :controller-overhead-measured-at-256-only
                              :thread-allocation-not-retained-memory :no-latency-guarantee]}]
    (spit "experiments/adaptive_affine/residual.clj.txt" (with-out-str (pp/pprint (:form info))))
    (spit "experiments/adaptive_affine/results.edn" (with-out-str (pp/pprint result)))
    (pp/pprint (update result :rows #(mapv (fn [row] (update row :measurements
                                                         (fn [m] (update-vals m (fn [v] (dissoc v :samples :value)))))) %)))
    result))
