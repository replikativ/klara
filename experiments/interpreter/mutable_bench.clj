(ns interpreter.mutable-bench
  (:require [clojure.test :as test] [clojure.java.io :as io] [clojure.pprint :as pp]
            [interpreter.mutable :as m] [interpreter.mutable-checks]
            [interpreter.run :as driver] [klara.eval :as ev]
            [klara.expand :as x] [klara.world :as w] [klara.core :as core])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]))

(def workloads
  (vec (concat
         (for [w driver/workloads :when (#{:sum :calls :persistent-update} (:name w))]
           (assoc w :n 10000))
         [{:name :nested-loop :n 10000 :form (nth interpreter.mutable-checks/programs 4)}
          {:name :closures :n 10000 :form (nth interpreter.mutable-checks/programs 3)}
          {:name :non-tail-recursion :n 16 :form (nth interpreter.mutable-checks/programs 1)}])))

(defn- measured [^ThreadMXBean bean f n]
  (let [id (.threadId (Thread/currentThread)) sink (volatile! nil)
        before (.getThreadAllocatedBytes bean id) start (System/nanoTime)]
    (dotimes [_ 5] (vreset! sink (f n)))
    {:ns-per-call (/ (- (System/nanoTime) start) 5.0)
     :bytes-per-call (/ (- (.getThreadAllocatedBytes bean id) before) 5.0) :value @sink}))

(defn benchmark [process {:keys [name n form]}]
  (let [term (x/expand-expr form w/empty-root)
        t (System/nanoTime) mf (m/prepare term) prepare (- (System/nanoTime) t)
        functions {:t0 (ev/run term) :mutable #(m/invoke mf %)
                   :clojure (binding [*ns* (the-ns 'interpreter.mutable-bench)] (eval form))}
        expected ((:clojure functions) n)
        bean ^ThreadMXBean (ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        _ (dotimes [_ 40] (doseq [engine [:clojure :t0 :mutable]]
                           (assert (= expected ((functions engine) n)))))
        samples (mapv (fn [i]
                        (let [order (vec (take 3 (drop (mod (+ i process) 3)
                                                       (cycle [:clojure :t0 :mutable]))))]
                          (into {} (for [engine order] [engine (measured bean (functions engine) n)]))))
                      (range 9))]
    (assert (every? #(= expected (:value %)) (mapcat vals samples)))
    {:workload name :n n :expected expected :mutable-prepare-ns prepare
     :engines (into {} (for [engine [:clojure :t0 :mutable]
                            :let [values (mapv engine samples)]]
                        [engine {:median-ns (driver/median (map :ns-per-call values))
                                 :median-bytes (driver/median (map :bytes-per-call values))
                                 :samples values}]))}))

(defn -main [& [process]]
  (if (= process "--check")
    (do (require 'interpreter.bridge-checks 'interpreter.activation-checks)
        (let [r (test/run-tests 'interpreter.mutable-checks 'interpreter.bridge-checks 'interpreter.activation-checks)]
          (when (pos? (+ (:fail r) (:error r))) (throw (ex-info "probe checks failed" r)))))
    (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil ev/*reference-driver* false]
      (let [process (Long/parseLong (or process "0")) rows (mapv #(benchmark process %) workloads)
            sources (concat ["deps.edn" "experiments/interpreter/run.clj"
                             "experiments/interpreter/mutable.clj" "experiments/interpreter/mutable_checks.clj"
                             "experiments/interpreter/mutable_bench.clj"]
                            (map str (filter #(.isFile %) (file-seq (io/file "src")))))
            report {:process process :java (System/getProperty "java.runtime.version")
                    :clojure (clojure-version) :compiler-cache false
                    :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
                    :measurement {:warmup 40 :samples 9 :calls-per-sample 5 :order :rotating}
                    :source-sha256 (into {} (for [p sources] [p (core/sha256 (slurp p))]))
                    :limits [:closed-pure-fragment :predecoded-Core :no-effects-or-global-resolution
                             :one-machine :not-guaranteed-steady-state :snapshot-cost-excluded]
                    :rows rows}
            output (str "target/interpreter/mutable-" process ".edn")]
        (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
        (doseq [row rows]
          (println (:workload row)
                   (into {} (for [[engine data] (:engines row)]
                              [engine (select-keys data [:median-ns :median-bytes])]))))
        (println :report output))))
  (shutdown-agents))
