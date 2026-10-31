(ns baseline.local-calls
  "REPL-friendly local-call diagnostic. No shutdown or external benchmark deps.
   Reports warm execution separately from preparation; not a cold-start study."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.compile.core :as compiler] [klara.compile.ir :as ir]
            [klara.compile.unbox :as unbox] [klara.core :as core]
            [klara.defs :as defs] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as world]))

(def source
  '(fn [n] (let [score (fn [x] (+ (* x x) 1))]
             (loop [i 0 total 0]
               (if (< i n) (recur (inc i) (+ total (score i))) total)))))

(defn- median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))

(defn- elapsed [f]
  (let [started (System/nanoTime) result (f)]
    {:value result :ns (- (System/nanoTime) started)}))

(defn- with-engine [prepared f]
  (if-let [cache (:cache prepared)]
    (stage/with-cache cache (f))
    (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil] (f))))

(defn- sample [prepared n repetitions]
  (let [bean ^com.sun.management.ThreadMXBean
        (java.lang.management.ManagementFactory/getThreadMXBean)
        thread (.threadId (Thread/currentThread))]
    (with-engine prepared
      #(let [before (.getThreadAllocatedBytes bean thread)
             sink (volatile! nil)
             measurement (elapsed (fn [] (dotimes [_ repetitions]
                                           (vreset! sink ((:function prepared) n)))))]
         {:ns-per-call (/ (:ns measurement) (double repetitions))
          :bytes-per-call (/ (- (.getThreadAllocatedBytes bean thread) before) (double repetitions))
          :value @sink}))))

(defn run-study!
  "Run after focused checks in an existing host REPL. Preserve each report by
   giving it a distinct label; fresh-process runs use -main."
  [label]
  (let [w (world/make-world) _ (defs/define! w (list 'def 'subject source))
        root (world/snapshot w) f (:value (world/entry* root 'subject))
        host (elapsed #(binding [*ns* (the-ns 'baseline.local-calls)] (eval source)))
        compilation (elapsed #(compiler/compile-def root 'subject {}))
        candidate (:value compilation) cache (stage/make-cache)
        installation (elapsed #(stage/install! cache candidate))
        baseline (try (compiler/compile-def root 'subject {:mode :baseline}) :accepted
                      (catch clojure.lang.ExceptionInfo ex (select-keys (ex-data ex) [:reason :message])))
        variants {:clojure {:function (:value host)} :t0 {:function f}
                  :optimizing {:function f :cache cache}}
        n 10000 expected 333283345000
        warmup {:clojure 2000 :optimizing 2000 :t0 20}
        repetitions {:clojure 100 :optimizing 100 :t0 1}
        bean ^com.sun.management.ThreadMXBean
        (java.lang.management.ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        _ (doseq [[engine prepared] variants]
            (with-engine prepared
              #(dotimes [_ (warmup engine)] (assert (= expected ((:function prepared) n))))))
        engines (vec (sort (keys variants)))
        samples (mapv (fn [i]
                        (into {} (for [engine (take (count engines) (drop i (cycle engines)))]
                                   [engine (sample (variants engine) n (repetitions engine))])))
                      (range 9))
        _ (assert (every? #(= expected (:value %)) (mapcat vals samples)))
        _ (assert (pos? (:hits (stage/stats cache))))
        _ (assert (zero? (:fallbacks (stage/stats cache))))
        _ (assert (zero? (:deopts (stage/stats cache))))
        report {:label label :java (System/getProperty "java.runtime.version")
                :vm (System/getProperty "java.vm.name") :clojure (clojure-version)
                :jvm-arguments (vec (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean)))
                :source source :n n :expected expected :warmup warmup :repetitions repetitions
                :limits [:warm-process :one-machine :current-thread-allocation
                         :no-cold-start-claim :no-interpreter-improvement]
                :preparation-ns {:clojure (:ns host) :optimizing (:ns compilation)
                                 :installation (:ns installation)}
                :baseline baseline :allocations-removed (:allocations-removed candidate)
                :emitted-form (binding [*print-meta* true] (pr-str (:form candidate)))
                :loop-layouts (mapv #(unbox/loop-kinds % {})
                                    (filter #(= :letrec (:op %)) (ir/nodes (:ir candidate))))
                :stats (stage/stats cache)
                :source-sha256 (into {} (for [file (concat [(io/file "experiments/baseline/local_calls.clj")]
                                                         (filter #(.isFile %) (file-seq (io/file "src"))))]
                                         [(str file) (core/sha256 (slurp file))]))
                :engines (into {} (for [engine engines :let [rows (mapv engine samples)]]
                                    [engine {:median-ns (median (map :ns-per-call rows))
                                             :median-bytes (median (map :bytes-per-call rows))
                                             :samples rows}]))}
        path (str "target/local-calls/" label ".edn")]
    (io/make-parents path)
    (spit path (with-out-str (pp/pprint report)))
    (select-keys report [:label :preparation-ns :baseline :allocations-removed :loop-layouts :stats :engines])))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))))
