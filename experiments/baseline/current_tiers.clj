(ns baseline.current-tiers
  "Current generic tiers and external controls, warmed together in one JVM."
  (:require [baseline.run :as base] [interpreter.bridge :as bridge]
            [interpreter.activation :as activation] [klara.eval :as ev]
            [klara.expand :as expand] [klara.world :as world] [klara.core :as core]
            [clojure.java.io :as io] [clojure.pprint :as pp])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]))

(def engines [:clojure :sci :t0 :nodes :activation])

(defn prepare [form]
  (let [term (expand/expand-expr form world/empty-root)]
    (reduce (fn [result engine]
              (assoc result engine
                     (try {:value (case engine
                                    :clojure (:value (base/prepare :clojure form))
                                    :sci (:value (base/prepare :sci form))
                                    :t0 (:value (base/prepare :klara form))
                                    :nodes (let [a (bridge/prepare term)] #(bridge/invoke a %))
                                    :activation (let [a (activation/prepare term)] #(bridge/invoke a %)))}
                          (catch clojure.lang.ExceptionInfo t
                            (if (and (#{:nodes :activation} engine)
                                     (or (:decline (ex-data t)) (:bridge/decline (ex-data t))))
                              {:unsupported (ex-data t)} (throw t)))))) {} engines)))

(defn measure [^ThreadMXBean bean f n]
  (let [id (.threadId (Thread/currentThread)) sink (volatile! nil)
        before (.getThreadAllocatedBytes bean id) start (System/nanoTime)]
    (dotimes [_ 5] (vreset! sink (f n)))
    {:ns-per-call (/ (- (System/nanoTime) start) 5.0)
     :bytes-per-call (/ (- (.getThreadAllocatedBytes bean id) before) 5.0) :value @sink}))

(defn workload [process [name form]]
  (let [prepared (prepare form) active (filterv #(get-in prepared [% :value]) engines)
        bean ^ThreadMXBean (ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)]
    (mapv
      (fn [n]
        (let [expected ((get-in prepared [:clojure :value]) n)
              ;; Interleave warmup so slower T0 also gives the host compiler
              ;; time to finish compiling the smaller/faster control kernels.
              _ (dotimes [i 200]
                  (doseq [e (take (count active) (drop (mod (+ i process) (count active)) (cycle active)))]
                    (assert (= expected ((get-in prepared [e :value]) n)))))
              pairs (mapv (fn [i]
                            (into {} (for [e (take (count active)
                                                     (drop (mod (+ i process) (count active)) (cycle active)))]
                                       [e (measure bean (get-in prepared [e :value]) n)]))) (range 9))]
          (assert (every? #(= expected (:value %)) (mapcat vals pairs)))
          {:workload name :n n :expected expected
           :unsupported (into {} (keep (fn [[e p]] (when (:unsupported p) [e (:unsupported p)]))) prepared)
           :engines (into {} (for [e active :let [samples (mapv e pairs)]]
                              [e {:median-ns (base/median (map :ns-per-call samples))
                                  :median-bytes (base/median (map :bytes-per-call samples))
                                  :samples samples}]))})) [1000 10000])))

(defn -main [& [process]]
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil ev/*reference-driver* false]
    (let [process (Long/parseLong (or process "0"))
          rows (vec (mapcat #(workload process %) (sort-by key base/workloads)))
          sources (concat ["deps.edn" "experiments/baseline/run.clj" "experiments/baseline/current_tiers.clj"
                           "experiments/interpreter/mutable.clj" "experiments/interpreter/activation.clj"
                           "experiments/interpreter/bridge.clj"]
                          (map str (filter #(.isFile %) (file-seq (io/file "src")))))
          report {:process process :java (System/getProperty "java.runtime.version")
                  :clojure (clojure-version) :sci "0.15.59" :compiler-cache false
                  :measurement {:warmup-per-engine-per-size 200 :samples 9 :calls-per-sample 5
                                :order :rotating :preparation-excluded true :allocation :current-thread-only}
                  :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
                  :source-sha256 (into {} (for [p sources] [p (core/sha256 (slurp p))]))
                  :limits [:one-machine :shared-fragment :not-guaranteed-steady-state
                           :experimental-private-tiers-have-less-language-coverage
                           :unsupported-is-not-fallback :retained-heap-not-measured]
                  :rows rows}
          output (str "target/baseline/current-tiers-" process ".edn")]
      (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
      (doseq [r rows]
        (println (:workload r) (:n r)
                 (into {} (for [[e d] (:engines r)] [e (select-keys d [:median-ns :median-bytes])]))))
      (println :report output)))
  (shutdown-agents))
