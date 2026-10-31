(ns interpreter.counted-loop-bench
  (:require [consolidation.counted-loop :as loop] [consolidation.counted-loop-model :as model]
            [interpreter.bridge :as bridge] [klara.core :as c] [klara.eval :as ev] [klara.world :as w]
            [clojure.java.io :as io] [clojure.pprint :as pp])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]))

(def workloads
  [{:name :sum :rhs (c/prim '+ (c/local 0) (c/local 1))
    :form '(fn [n] (loop [i 0 s 0] (if (< i n) (recur (+ i 1) (+ s i)) s)))}
   {:name :sum-squares :rhs (c/prim '+ (c/local 0) (c/prim '* (c/local 1) (c/local 1)))
    :form '(fn [n] (loop [i 0 s 0] (if (< i n) (recur (+ i 1) (+ s (* i i))) s)))}])
(def engine-order [:clojure :generic-body :primitive-body :generic :primitive :nodes :t0 :reference])
(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
(defn timed [f] (let [start (System/nanoTime) value (f)] {:ns (- (System/nanoTime) start) :value value}))
(defn prepare [{:keys [rhs form]}]
  (let [source (loop/source rhs)
        proof (timed #(loop/certify source))
        emission (timed #(loop/prepare-certified source w/empty-root (:value proof)))
        artifact (:value emission)
        nodes (timed #(bridge/prepare source))
        t0 (timed #(ev/run source))
        host (timed #(eval form))
        f (:value t0)]
    {:source source :forms (:forms artifact)
     :preparation-ns {:certificate (:ns proof) :admission-and-both-emitters (:ns emission)
                      :nodes (:ns nodes) :t0-entry (:ns t0) :clojure (:ns host)}
     :engines {:clojure (:value host)
               :generic-body #(nth ((get-in artifact [:bodies :generic]) % 0 0 Long/MAX_VALUE) 2)
               :primitive-body #(nth ((get-in artifact [:bodies :primitive]) % 0 0 Long/MAX_VALUE) 2)
               :generic #(loop/invoke artifact % :generic)
               :primitive #(loop/invoke artifact % :primitive)
               :nodes #(bridge/invoke (:value nodes) %)
               :t0 #(binding [ev/*reference-driver* false] (f %))
               :reference #(binding [ev/*reference-driver* true] (f %))}}))
(defn measure [^ThreadMXBean bean f n]
  (let [thread (.threadId (Thread/currentThread)) sink (volatile! nil)
        bytes (.getThreadAllocatedBytes bean thread) start (System/nanoTime)]
    (dotimes [_ 10] (vreset! sink (f n)))
    {:ns (/ (- (System/nanoTime) start) 10.0)
     :bytes (/ (- (.getThreadAllocatedBytes bean thread) bytes) 10.0)
     :value @sink}))
(defn run-workload [process {:keys [name] :as workload}]
  (let [{:keys [engines preparation-ns source forms]} (prepare workload)
        ^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        order (fn [i] (take (count engine-order)
                           (drop (mod (+ process i) (count engine-order)) (cycle engine-order))))]
    {:name name :source source :forms forms :preparation-ns preparation-ns
     :rows (mapv (fn [n]
                   (let [expected ((engines :clojure) n)
                         _ (dotimes [i 200] (doseq [engine (order i)] (assert (= expected ((engines engine) n)))))
                         samples (mapv (fn [i] (into {} (for [engine (order i)]
                                                           [engine (measure bean (engines engine) n)]))) (range 9))]
                     (assert (every? #(= expected (:value %)) (mapcat vals samples)))
                     {:n n :expected expected
                      :engines (into {} (for [engine engine-order :let [values (mapv engine samples)]]
                                          [engine {:median-ns (median (map :ns values))
                                                   :median-bytes (median (map :bytes values)) :samples values}]))}))
                 [1000 10000])}))
(defn -main [& [process]]
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
    (let [process (Long/parseLong (or process "0"))
          bootstrap (timed #(force model/proof-state))
          reports (mapv #(run-workload process %) workloads)
          sources (cons "deps.edn"
                        (mapcat (fn [dir] (map str (filter #(and (.isFile %) (.endsWith (str %) ".clj"))
                                                          (file-seq (io/file dir)))))
                                ["src" "experiments/consolidation" "experiments/interpreter"]))
          report {:process process :java (System/getProperty "java.runtime.version") :clojure (clojure-version)
                  :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
                  :source-sha256 (into (sorted-map) (map (fn [p] [p (c/sha256 (slurp p))]) sources))
                  :model-bootstrap-ns (:ns bootstrap)
                  :measurement {:warmup-per-engine-per-size 200 :samples 9 :calls-per-sample 10 :order :rotating}
                  :limits [:closed-two-state-scalar-fragment :one-machine :not-guaranteed-steady-state
                           :no-GC-or-retained-heap-profile :body-only-excludes-entry-guards
                           :no-compiled-interior-recovery :compilation-preparation-measured-once]
                  :workloads reports}
          path (str "target/counted-loop/process-" process ".edn")]
      (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
      (doseq [work reports row (:rows work)]
        (println (:name work) (:n row) (into {} (for [[e d] (:engines row)] [e (:median-ns d)]))))
      (println :report path)))
  (shutdown-agents))
