(ns consolidation.benchmark
  "Independent-process diagnostic for the composed native candidate. Raw
   samples include full guarded invocation; this is not a benchmark corpus."
  (:require [clojure.java.io :as io]
            [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.pprint :as pp]
            [consolidation.checked-pipeline :as pipeline]
            [klara.compile.staged :as staged]
            [klara.core :as c]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w]
            [proof-staging :as ps])
  (:import [java.lang.management ManagementFactory]))

(defn polynomial ^long [^long x] (+ 1 (* x (+ 2 (* x 3)))))
(defn functional [xs]
  (nth (reduce (fn [a x] (assoc a 0 (+ (long (nth a 0)) (polynomial (long x))))) [0] xs) 0))
(defn transient-sum [xs]
  (nth (persistent! (reduce (fn [a x] (assoc! a 0 (+ (long (nth a 0)) (polynomial (long x)))))
                           (transient [0]) xs)) 0))
(defn primitive [xs]
  (let [n (count xs)]
    (loop [i (long 0) sum (long 0)]
      (if (< i n) (recur (inc i) (+ sum (polynomial (long (nth xs i))))) sum))))
(defn mapped [xs] (reduce + 0 (map polynomial xs)))
(def ^com.sun.management.ThreadMXBean allocation-bean (ManagementFactory/getThreadMXBean))
(defn allocated [] (.getThreadAllocatedBytes allocation-bean (.threadId (Thread/currentThread))))
(defn median [xs] (nth (sort xs) (quot (count xs) 2)))

(defn sample [iterations f]
  (let [sink (volatile! nil) bytes (allocated) start (System/nanoTime)]
    (dotimes [_ iterations] (vreset! sink (f)))
    {:ns (/ (- (System/nanoTime) start) (double iterations))
     :bytes (/ (- (allocated) bytes) (double iterations)) :value @sink :iterations iterations}))
(defn timed [f]
  (let [start (System/nanoTime) v (f)] {:value v :ms (/ (- (System/nanoTime) start) 1e6)}))

(defn run-process! [id]
  (let [generation (timed #(ps/proposals [1 2 3])) p (:value generation)
        request {:source (:source p) :targets [(:numeric p) (:both p)]
                 :steps [{:kind :numeric :coefficients [1 2 3]} {:kind :fusion}]
                 :domain {:max-count 4096 :max-x 100} :executor :private-array}
        preparation (timed #(pipeline/prepare w/empty-root request)) candidate (:value preparation)
        info (staged/prepared-info candidate) cache (stage/make-cache)
        installation (timed #(staged/install! cache w/empty-root candidate))
        source (ev/run (ps/core-term (:source p)) {:basis w/empty-root})
        body (binding [*unchecked-math* false *ns* (the-ns 'klara.compile.affine-erase)]
               (eval (get-in info [:native-info :form])))
        functions [[:mapped mapped] [:functional functional] [:transient transient-sum] [:primitive primitive]
                   [:emitted-body #(nth (body %) 0)]
                   [:guarded #(stage/with-cache cache (ev/call-value source [%]))]
                   [:guard-scan #(stage/argument-holds? [:bounded-nat-vector 4096 100] %)]
                   [:T0 #(binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
                           (ev/call-value source [%]))]]
        ;; Warm every size before measuring any size. Otherwise small rows see
        ;; earlier compiler tiers than large rows of the SAME residual method.
        _ (doseq [n [16 256 4096]
                  :let [xs (mapv #(long (mod % 101)) (range n))]
                  [label f] functions]
            (dotimes [_ (if (= label :T0) 8 3000)] (f xs)))
        rows (mapv
               (fn [n]
                 (let [xs (mapv #(long (mod % 101)) (range n)) expected (primitive xs)
                       samples
                       (reduce
                         (fn [out batch]
                           (reduce
                             (fn [out [label f]]
                               (let [s (sample (if (= label :T0) 2 200) #(f xs))]
                                 (assert (= (if (= label :guard-scan) true expected) (:value s)))
                                 (update out label (fnil conj []) s))) out
                             (if (even? (+ batch id)) functions (reverse functions)))) {} (range 9))]
                   {:n n :measurements (update-vals samples
                                          (fn [ss] {:median-ns (median (map :ns ss))
                                                    :median-bytes (median (map :bytes ss)) :samples ss}))}))
               [16 256 4096])
        declined (timed #(try (pipeline/prepare w/empty-root (assoc-in request [:steps 0 :coefficients] [1 2 4]))
                              :unexpected (catch clojure.lang.ExceptionInfo _ :declined)))
        ;; Investment policy costs use the same source and same total result.
        inputs (vec (repeat 4 (vec (range 16))))
        policy (fn [kind]
                 (let [cache (stage/make-cache)]
                   (reduce (fn [total [index xs]]
                             (when (or (= kind :always) (and (= kind :bounded) (= index 1)))
                               (staged/install! cache w/empty-root (pipeline/prepare w/empty-root request)))
                             (+ total (stage/with-cache cache (ev/call-value source [xs]))))
                           0 (map-indexed vector inputs))))
        policies (into {} (map (fn [kind] [kind (timed #(policy kind))]) [:never :always :bounded]))
        output (str "experiments/consolidation/benchmark-process-" id ".edn")
        report {:process id :java (System/getProperty "java.runtime.version")
                :vm (System/getProperty "java.vm.name") :processors (.availableProcessors (Runtime/getRuntime))
                :warmup {:calls-per-size 3000 :T0-calls-per-size 8 :all-sizes-before-sampling true}
                :sampling {:batches 9 :iterations 200 :T0-iterations 2 :order :alternating-process-parity}
                :generation-ms (:ms generation) :preparation-ms (:ms preparation)
                :installation-ms (:ms installation) :declined declined :policies policies
                :phases (select-keys info [:proof-and-bounds-ms :shared-bootstrap-ms])
                :native-phases (select-keys (:native-info info) [:analysis-ms :erasure-ms :emission-and-loading-ms])
                :rows rows :source-id (c/code-id (ps/core-term (:source p)))
                :limitations [:single-workload-family :three-process-pilot :no-cpu-isolation
                              :thread-allocation-not-retained-memory :guard-scan-is-linear
                              :T0-has-less-warmup :no-cold-JVM-end-to-end :no-throughput-concurrency]}]
    (spit output (with-out-str (pp/pprint report)))
    (spit (str "experiments/consolidation/native-residual-" id ".clj.txt")
          (binding [*print-meta* true] (with-out-str (pp/pprint (get-in info [:native-info :form])))))
    (println :benchmark-written output)
    report))

(defn -main [id] (run-process! (Long/parseLong id)) (shutdown-agents))

(defn summarize! [ids]
  (let [reports (mapv #(edn/read-string (slurp (str "experiments/consolidation/benchmark-process-" % ".edn"))) ids)
        range-summary (fn [values] {:median (median values) :min (apply min values) :max (apply max values)})
        rows (mapv (fn [i]
                     {:n (get-in (first reports) [:rows i :n])
                      :measurements (into {}
                                      (for [label (keys (get-in (first reports) [:rows i :measurements]))]
                                        [label {:ns (range-summary (map #(get-in % [:rows i :measurements label :median-ns]) reports))
                                                :bytes (range-summary (map #(get-in % [:rows i :measurements label :median-bytes]) reports))}]))})
                   (range (count (:rows (first reports)))))
        source-paths ["src/klara/stage.clj" "src/klara/compile/analysis.clj" "src/klara/compile/updates.clj"
                      "src/klara/compile/infer_affine.clj" "src/klara/compile/affine_erase.clj"
                      "src/klara/compile/strict_fold.clj" "experiments/consolidation/checked_pipeline.clj"
                      "experiments/consolidation/fold_model.clj" "experiments/proof_staging/proof_staging.clj"]
        result {:processes ids :aggregation :median-and-range-of-process-medians :rows rows
                :hardware "Intel Core Ultra 7 258V, x86_64, 8 cores; no CPU pinning"
                :source-sha256 (into {} (map (fn [p] [p (c/sha256 (slurp p))]) source-paths))
                :preparation-ms (range-summary (map :preparation-ms reports))
                :installation-ms (range-summary (map :installation-ms reports))
                :limitations (:limitations (first reports))}
        labels [:mapped :functional :transient :primitive :emitted-body :guarded :guard-scan :T0]
        cell (fn [r label] (let [{:keys [median min max]} (get-in r [:measurements label :ns])]
                            (format "%.2f [%.2f, %.2f]" (/ median 1000.0) (/ min 1000.0) (/ max 1000.0))))
        markdown (str "# Native composition: independent-process pilot\n\n"
                      "Intel Core Ultra 7 258V, 8 cores. Processes " (pr-str ids)
                      "; no CPU pinning. Times are microseconds per invocation: median [min, max] of three process medians. Ranges describe variability, not confidence intervals.\n\n"
                      "| n | mapped | functional vector | transient | primitive scalar | emitted body | full guarded | guard scan | T0 |\n"
                      "|---|---|---|---|---|---|---|---|---|\n"
                      (apply str (for [r rows] (str "| " (:n r) " | " (str/join " | " (map #(cell r %) labels)) " |\n")))
                      "\nPreparation (ms): " (pr-str (:preparation-ms result)) ". Installation (ms): " (pr-str (:installation-ms result)) ".\n\n"
                      "Raw samples, thread allocation, policy costs and phase timings are in the process EDN files. Never/always/bounded policies return the same result; short workloads cannot amortize repeated preparation. T0 receives less warmup. The body result alone is not an end-to-end speedup.\n\n"
                      "Processes 0–5 preserve development versions of guards, layouts and prover bootstrap. Process 6 uses the final compiler with the earlier per-row warmup protocol. They are excluded from this aggregate. The final protocol warms every size before measuring any size to reduce compiler-tier differences between rows. This is one workload family on one machine, not a broad workload evaluation.\n")]
    (spit "experiments/consolidation/benchmark-summary.edn" (with-out-str (pp/pprint result)))
    (spit "experiments/consolidation/benchmark-summary.md" markdown)
    result))
