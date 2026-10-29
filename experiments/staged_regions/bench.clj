(ns staged-regions.bench
  "Diagnostic lifecycle measurements, not a publication benchmark.
   Run in a persistent REPL: (load-file \"experiments/staged_regions/bench.clj\")
   then (staged-regions.bench/run!). No JVM restarts or background warmup."
  (:refer-clojure :exclude [run!])
  (:require [clojure.java.io :as io]
            [clojure.pprint :as pp]
            [klara.authority :as a]
            [klara.compile.staged :as sc]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w]))

(defn load-world []
  (let [wo (w/make-world)]
    (with-open [r (java.io.PushbackReader. (io/reader "examples/staging/07-staged-regions.klr"))]
      (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} r)))]
        (d/define! wo form))) wo))

;; Independent ordinary Clojure baseline, with primitive loop state. It uses
;; the same checked operation order; no algebraic reassociation or unchecked math.
(defn clojure-kernel ^long [^long n ^long offset]
  (loop [i (long 0) score (long 0)]
    (if (< i n)
      (let [residual (- (+ 3 (* i (+ -2 (* i (+ 1 (* i 0)))))) offset)]
        (recur (inc i) (+ score (* residual residual))))
      score)))

(defn measure [warm iterations batches f]
  (let [sink (volatile! nil)]
    (dotimes [_ warm] (vreset! sink (f)))
    (let [samples (vec (repeatedly batches
                         #(let [start (System/nanoTime)]
                            (dotimes [_ iterations] (vreset! sink (f)))
                            (/ (- (System/nanoTime) start) (double iterations)))))]
      {:median-ns (nth (sort samples) (quot batches 2))
       :samples-ns samples :value @sink :calls (* iterations batches)})))

(defn run! []
  (let [early-start (System/nanoTime) wo (load-world)
        early-ms (/ (- (System/nanoTime) early-start) 1e6)
        root (w/snapshot wo) source (d/lookup root 'kernel-code)
        f (d/lookup root 'kernel) cache (stage/make-cache)
        prepared (sc/prepare root source)
        info (sc/prepared-info prepared)
        install-start (System/nanoTime)
        _ (sc/install! cache root prepared)
        install-ms (/ (- (System/nanoTime) install-start) 1e6)
        ;; Warm both entry paths across all sizes before taking any row. The
        ;; earlier fixed-order probe visibly compiled its baseline mid-table.
        _ (doseq [n [32 256 1024]]
            (dotimes [_ 30000] (clojure-kernel n 4))
            (stage/with-cache cache (dotimes [_ 10000] (ev/call-value f [n]))))
        rows (mapv
               (fn [n]
                 (let [baseline (measure 5000 2000 7 #(clojure-kernel n 4))
                       compiled (stage/with-cache cache
                                  (measure 3000 1000 7 #(ev/call-value f [n])))
                       generic (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
                                 (measure 8 12 7 #(ev/call-value f [n])))
                       saving (- (:median-ns generic) (:median-ns compiled))]
                   (assert (= (:value baseline) (:value generic) (:value compiled)))
                   {:n n :clojure baseline :staged-jvm compiled :t0 generic
                    :diagnostic-break-even-calls
                    (when (pos? saving) (long (Math/ceil (/ (* 1e6 (:compile-ms info)) saving))))}))
               [32 256 1024])
        result {:runtime {:java (System/getProperty "java.runtime.version")
                          :vm (System/getProperty "java.vm.name")
                          :jvmci (.getValue (.getVMOption
                                            (java.lang.management.ManagementFactory/getPlatformMXBean
                                             com.sun.management.HotSpotDiagnosticMXBean)
                                            "UseJVMCICompiler"))}
                :early-generator-and-definitions-ms early-ms
                :compile-ms (:compile-ms info) :install-ms install-ms
                :class-bytes (:class-bytes info) :cache-stats (stage/stats cache)
                :rows rows
                :limitations [:single-process :fixed-order :diagnostic-only
                              :no-memory-retention-measurement :synchronous-example-policy
                              :break-even-excludes-generator-and-profile-cost]}]
    (spit "experiments/staged_regions/kernel.java.txt" (:java-source info))
    (spit "experiments/staged_regions/results.edn" (with-out-str (pp/pprint result)))
    (pp/pprint result)
    result))
