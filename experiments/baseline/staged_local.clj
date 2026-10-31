(ns baseline.staged-local
  "REPL-friendly checked guest-analysis diagnostic; no interpreter shutdown."
  (:require [baseline.local-calls :as reference]
            [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.compile.budget :as budget] [klara.compile.core :as compiler]
            [klara.core :as core] [klara.defs :as defs] [klara.eval :as ev]
            [klara.load :as load] [klara.stage :as stage] [klara.world :as world]))

(defn- elapsed [f]
  (let [started (System/nanoTime) result (f)] {:value result :ns (- (System/nanoTime) started)}))

(defn- sample [prepared n repetitions]
  (let [^com.sun.management.ThreadMXBean bean (java.lang.management.ManagementFactory/getThreadMXBean)
        run (fn []
              (let [before (.getThreadAllocatedBytes bean (.threadId (Thread/currentThread)))
                    sink (volatile! nil)
                    measured (elapsed #(dotimes [_ repetitions] (vreset! sink ((:function prepared) n))))]
                {:value @sink :ns-per-call (/ (:ns measured) (double repetitions))
                 :bytes-per-call (/ (- (.getThreadAllocatedBytes bean (.threadId (Thread/currentThread))) before)
                                    (double repetitions))}))]
    (if (:cache prepared) (stage/with-cache (:cache prepared) (run))
      (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil] (run)))))

(defn- compiled [root f options]
  (let [b (budget/budget) result (elapsed #(compiler/compile-def root 'subject (assoc options :budget b)))
        exe (:value result) cache (stage/make-cache)
        installation (elapsed #(stage/install! cache exe))]
    {:function f :cache cache :executable exe
     :preparation {:compile-ns (:ns result) :validation-installation-ns (:ns installation)
                   :usage (budget/usage b)}}))

(defn run-study! [label]
  (let [w (world/make-world) _ (defs/define! w (list 'def 'subject reference/source))
        loading (elapsed #(load/load-file! w "examples/compat/klara/local_optimizer.cljc" {}))
        root (world/snapshot w) f (defs/lookup root 'subject)
        clj (elapsed #(binding [*ns* (the-ns 'baseline.staged-local)] (eval reference/source)))
        variants {:clojure {:function (:value clj) :preparation {:compile-ns (:ns clj)}}
                  :optimizing (compiled root f {})
                  :guest-staged (compiled root f {:mode :baseline :local-call-planner 'klara.local-optimizer/planner})}
        n 10000 expected 333283345000
        bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        engines (vec (sort (keys variants)))
        _ (dotimes [i 2000]
            (doseq [engine (take (count engines) (drop (mod i (count engines)) (cycle engines)))]
              (assert (= expected (:value (sample (variants engine) n 1))))))
        samples (mapv (fn [i] (into {} (for [engine (take (count engines) (drop i (cycle engines)))]
                                        [engine (sample (variants engine) n 100)]))) (range 9))
        _ (assert (every? #(= expected (:value %)) (mapcat vals samples)))
        _ (doseq [[_ p] variants :when (:cache p)]
            (assert (pos? (:hits (stage/stats (:cache p)))))
            (assert (zero? (:fallbacks (stage/stats (:cache p)))))
            (assert (zero? (:deopts (stage/stats (:cache p))))))
        report {:label label :source reference/source :n n :expected expected
                :java (System/getProperty "java.runtime.version") :vm (System/getProperty "java.vm.name")
                :warmup 2000 :samples 9 :batch 100 :module-load-ns (:ns loading)
                :limits [:warm-process :one-program :current-thread-allocation
                         :no-cold-start-distribution :no-universal-correctness-proof]
                :engines
                (into {} (for [engine engines
                               :let [p (variants engine) rows (mapv engine samples)
                                     median #(nth (vec (sort %)) (quot (count %) 2))]]
                           [engine (cond-> {:median-ns (median (map :ns-per-call rows))
                                            :median-bytes (median (map :bytes-per-call rows))
                                            :samples rows :preparation (:preparation p)}
                                     (:cache p) (assoc :stats (stage/stats (:cache p))
                                                       :pass-log (get-in p [:executable :pass-log])
                                                       :rewrite-receipts (get-in p [:executable :rewrite-receipts])
                                                       :emitted-form (binding [*print-meta* true]
                                                                       (pr-str (get-in p [:executable :form])))))]))
                :source-sha256
                (into {} (for [path (concat ["experiments/baseline/staged_local.clj"
                                             "experiments/baseline/local_calls.clj"
                                             "examples/compat/klara/local_optimizer.cljc"]
                                            (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                           [path (core/sha256 (slurp path))]))}
        path (str "target/staged-local/" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    {:path path :module-load-ns (:module-load-ns report)
     :engines (into {} (for [[k v] (:engines report)]
                        [k (select-keys v [:median-ns :median-bytes :preparation :rewrite-receipts])]))}))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))))
