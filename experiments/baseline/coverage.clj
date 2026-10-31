(ns baseline.coverage
  "Wider data/call coverage, using the matched investment harness unchanged."
  (:require [baseline.investment :as investment] [baseline.run :as base]
            [klara.core :as core] [klara.eval :as ev] [klara.world :as world]
            [clojure.java.io :as io] [clojure.pprint :as pp]))

(def workloads
  {:histogram
   {:sizes [1000 10000]
    :form '(fn [n] (loop [i 0 counts {}]
                     (if (< i n)
                       (let [key (rem i 32)]
                         (recur (inc i) (assoc counts key (inc (get counts key 0))))) counts)))}
   :records
   {:sizes [1000 5000]
    :form '(fn [n]
             (let [rows (loop [i 0 rows []]
                          (if (< i n) (recur (inc i) (conj rows {:bucket (rem i 16) :value (* i i)})) rows))]
               (loop [i 0 totals {}]
                 (if (< i (count rows))
                   (let [row (nth rows i) bucket (get row :bucket)]
                     (recur (inc i) (assoc totals bucket (+ (get totals bucket 0) (get row :value))))) totals))))}
   :tree-worklist
   {:sizes [8 12]
    :form '(fn [depth]
             (let [tree (loop [d depth node [1]]
                          (if (> d 0) (recur (dec d) [node node]) node))]
               (loop [pending (list tree) total 0]
                 (if (empty? pending) total
                   (let [node (first pending) more (rest pending)]
                     (if (= (count node) 1)
                       (recur more (+ total (nth node 0)))
                       (recur (cons (first node) (cons (second node) more)) total)))))))}
   :local-callback
   {:sizes [1000 10000]
    :form '(fn [n] (let [score (fn [x] (+ (* x x) 1))]
                     (loop [i 0 total 0]
                       (if (< i n) (recur (inc i) (+ total (score i))) total))))}})

(def mutual
  '(fn [n] (letfn [(even [i] (if (= i 0) true (odd (dec i))))
                   (odd [i] (if (= i 0) false (even (dec i))))] (even n))))

(defn mutual-support [process]
  (let [prepared (:engines (investment/prepare mutual process))]
    (into {} (for [[engine p] prepared]
               [engine (if (:unsupported p) (select-keys p [:unsupported])
                         (mapv (fn [n]
                                 (try (let [v (investment/scope p #((:value p) n))]
                                        (assert (true? v)) {:n n :value v})
                                      (catch Throwable t
                                        (if (some #(instance? StackOverflowError %)
                                                  (take-while some? (iterate ex-cause t)))
                                          {:n n :error :stack-overflow :wrapper (.getName (class t))}
                                          (throw t))))) [64 10000]))]))))

(defn -main [& [process]]
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil ev/*reference-driver* false]
    (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
          _ (.setThreadAllocatedMemoryEnabled bean true)
          process (Long/parseLong (or process "0"))
          hashes (assoc (investment/source-hashes) "experiments/baseline/coverage.clj"
                        (core/sha256 (slurp "experiments/baseline/coverage.clj")))
          rows (mapv #(investment/workload process %) (sort-by key workloads))
          report {:process process :java (System/getProperty "java.runtime.version")
                  :jvm-arguments (vec (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean)))
                  :source-sha256 hashes :workloads rows :mutual-support (mutual-support process)
                  :measurement {:warmup 200 :samples 9 :small-batch 100 :large-batch 5
                                :order :rotating :mutual-support-not-timed true}}
          output (str "target/coverage/run-" process ".edn")]
      (assert (= hashes (assoc (investment/source-hashes) "experiments/baseline/coverage.clj"
                              (core/sha256 (slurp "experiments/baseline/coverage.clj")))))
      (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
      (println :mutual-support (:mutual-support report)) (println :report output)))
  (shutdown-agents))
