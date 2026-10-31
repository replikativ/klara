(ns interpreter.activation-bench
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [interpreter.activation :as a] [interpreter.bridge :as b]
            [interpreter.bridge-checks :as checks] [interpreter.mutable-bench :as cases]
            [interpreter.run :as driver] [klara.core :as core]
            [klara.expand :as x] [klara.world :as w])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]))

(def workloads
  (conj cases/workloads
        {:name :large-capture :n 10000
         :form (list 'fn '[n]
                     (list 'let
                           (vec (concat (mapcat (fn [i] [(symbol (str "v" i)) i]) (range 64))
                                        ['f '(fn [x] (+ x v0 v63))]))
                           '(loop [i 0 sum 0]
                              (if (< i n) (recur (inc i) (+ sum (f i))) sum))))}))

(defn sample [f repetitions]
  (let [bean ^ThreadMXBean (ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        id (.threadId (Thread/currentThread)) sink (volatile! nil)
        before (.getThreadAllocatedBytes bean id) start (System/nanoTime)]
    (dotimes [_ repetitions] (vreset! sink (f)))
    {:ns-per-call (/ (- (System/nanoTime) start) (double repetitions))
     :bytes-per-call (/ (- (.getThreadAllocatedBytes bean id) before) (double repetitions))
     :value @sink}))

(defn summarize [samples]
  {:median-ns (driver/median (map :ns-per-call samples))
   :median-bytes (driver/median (map :bytes-per-call samples)) :samples samples})

(defn- prepare-cost [prepare term]
  (dotimes [_ 5] (prepare term))
  (summarize (mapv (fn [_] (dissoc (sample #(prepare term) 1) :value)) (range 9))))

(defn benchmark [process {:keys [name form n]}]
  (let [term (x/expand-expr form w/empty-root)
        preparations {:nodes (prepare-cost b/prepare term) :activation (prepare-cost a/prepare term)}
        artifacts {:nodes (b/prepare term) :activation (a/prepare term)}
        expected ((binding [*ns* (the-ns 'interpreter.activation-bench)] (eval form)) n)
        operations (into {} (for [[engine artifact] artifacts] [engine #(b/invoke artifact n)]))
        _ (dotimes [_ 40] (doseq [engine [:nodes :activation]] (assert (= expected ((operations engine))))))
        pairs (mapv (fn [i]
                      (into {} (for [engine (if (even? (+ process i)) [:nodes :activation] [:activation :nodes])]
                                 [engine (sample (operations engine) 5)]))) (range 9))]
    (assert (every? #(= expected (:value %)) (mapcat vals pairs)))
    {:workload name :n n :expected expected :preparation preparations
     :program-structure
     (let [programs (vals (:programs (:activation artifacts)))]
       {:functions (count programs)
        :instructions (reduce + (map #(alength ^objects (.-code ^interpreter.activation.Program %)) programs))
        :slots (reduce + (map #(+ (.-locals ^interpreter.activation.Program %)
                                  (.-temps ^interpreter.activation.Program %)) programs))})
     :engines (into {} (for [engine [:nodes :activation]] [engine (summarize (mapv engine pairs))]))}))

(defn- materialized [c] (:state (b/transfer! (b/thaw (b/freeze c)))))

(defn matching-snapshots [term]
  (let [nodes (b/start (b/prepare term) [16]) activation (b/start (a/prepare term) [16])]
    (let [candidates
          (loop [i 0 found {}]
            (if (= i 800) found
              (let [state (materialized nodes)
                    found (if (and (= :eval (first state))
                                   (= :local (:op (second state)))
                                   (>= (count (nth state 3)) 8))
                            (assoc found (checks/signature state w/empty-root) (b/freeze nodes)) found)]
                (b/advance! nodes 1) (recur (inc i) found))))]
      (assert (seq candidates) "no deep node snapshot candidates")
      (loop [i 0]
        (assert (< i 800) "no equivalent activation snapshot")
        (let [state (materialized activation) signature (checks/signature state w/empty-root)]
          (if-let [snapshot (get candidates signature)]
            {:nodes (b/thaw snapshot) :activation activation
             :logical-frames (count (nth state 3)) :signature signature}
            (do (b/advance! activation 1) (recur (inc i)))))))))

(defn snapshot-cost [process]
  (let [term (x/expand-expr (:form (last cases/workloads)) w/empty-root)
        {:keys [nodes activation logical-frames]} (matching-snapshots term)
        states {:nodes nodes :activation activation}
        operations (into {} (for [[engine state] states] [engine #(b/thaw (b/freeze state))]))
        _ (doseq [engine [:nodes :activation]]
            (dotimes [_ 40] ((operations engine))))
        pairs (mapv (fn [i]
                      (into {} (for [engine (if (even? (+ process i)) [:nodes :activation] [:activation :nodes])]
                                 [engine (dissoc (sample (operations engine) 10) :value)]))) (range 9))]
    (doseq [state (vals states)] (assert (= 987 (b/resume! (b/transfer! state)))))
    {:workload :matched-fib-16 :logical-frames logical-frames
     :engines (into {} (for [engine [:nodes :activation]] [engine (summarize (mapv engine pairs))]))}))

(defn -main [& [process]]
  (let [process (Long/parseLong (or process "0")) rows (mapv #(benchmark process %) workloads)
        snapshots (snapshot-cost process)
        files (concat ["deps.edn"]
                      (map str (filter #(.isFile %) (file-seq (io/file "src"))))
                      (map str (filter #(and (.isFile %) (.endsWith (.getName %) ".clj"))
                                       (file-seq (io/file "experiments/interpreter")))))
        report {:process process :java (System/getProperty "java.runtime.version") :clojure (clojure-version)
                :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
                :os {:name (System/getProperty "os.name") :arch (System/getProperty "os.arch")
                     :version (System/getProperty "os.version")
                     :available-processors (.availableProcessors (Runtime/getRuntime))}
                :measurement {:warmup 40 :samples 9 :calls-per-sample 5 :order :alternating
                              :preparation :separate-warmed :snapshot-pair :freeze-and-thaw}
                :limits [:closed-pure-fragment :boxed-values :one-machine :not-guaranteed-steady-state
                         :retained-heap-not-measured :source-expansion-excluded]
                :source-sha256 (into {} (for [p files] [p (core/sha256 (slurp p))]))
                :rows rows :snapshots snapshots}
        output (str "target/interpreter/activation-" process ".edn")]
    (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
    (doseq [r (conj rows snapshots)]
      (println (:workload r) (into {} (for [[engine d] (:engines r)]
                                     [engine (select-keys d [:median-ns :median-bytes])]))))
    (println :report output))
  (shutdown-agents))
