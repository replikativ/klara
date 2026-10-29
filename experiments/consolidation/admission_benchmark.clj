(ns consolidation.admission-benchmark
  (:require [clojure.pprint :as pp] [clojure.edn :as edn]
            [consolidation.benchmark :as bench]
            [consolidation.producer-consumer :as pc]
            [consolidation.checked-pipeline :as pipeline]
            [klara.compile.staged :as staged] [klara.core :as c]
            [klara.infer-affine-test :as base] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as w] [proof-staging :as ps])
  (:import [java.util.concurrent.atomic LongAdder]))

(defn setup []
  (let [p (ps/proposals [1 2 3])
        request {:source (:source p) :targets [(:numeric p) (:both p)]
                 :steps [{:kind :numeric :coefficients [1 2 3]} {:kind :fusion}]
                 :domain {:max-count 4096 :max-x 100} :executor :private-array}
        preparation (bench/timed #(pipeline/prepare w/empty-root request)) candidate (:value preparation)
        cache (stage/make-cache) installation (bench/timed #(staged/install! cache w/empty-root candidate))
        legacy-installation (bench/timed #(stage/install! (stage/make-cache)
                                                         (.-executable ^klara.compile.staged.Prepared candidate)))
        f (ev/run (ps/core-term (:source p)) {:basis w/empty-root})]
    {:cache cache :closure f :consumer (pc/consumer cache f)
     :producer (pc/prepare-producer (base/source '(fn [x] (+ x 1))) 99)
     :preparation-ms (:ms preparation) :publication-ms (:ms installation)
     :legacy-checked-installation-ms (:ms legacy-installation)
     :validation-ms (:validation-ms (staged/prepared-info candidate))}))

(defn profile-guards [ctx]
  (let [counts (into {} (for [k [:world :arg :host-root :captures :statics :arity :unhandled]]
                          [k [(LongAdder.) (LongAdder.)]]))
        original stage/guard-holds? xs (vec (range 64))]
    (with-redefs [stage/guard-holds? (fn [guard env]
                                     (let [start (System/nanoTime) result (original guard env)
                                           elapsed (- (System/nanoTime) start) [n ns] (counts (first guard))]
                                       (when n (.increment ^LongAdder n) (.add ^LongAdder ns elapsed)) result))]
      (dotimes [_ 1000] (stage/with-cache (:cache ctx) (ev/call-value (:closure ctx) [xs]))))
    (update-vals counts (fn [[n ns]] {:checks (.sum ^LongAdder n) :instrumented-ns (.sum ^LongAdder ns)}))))

(defn run-process! [id]
  (let [ctx (setup)
        cases (mapv
                (fn [n]
                  (let [xs (mapv #(long (mod % 100)) (range n))
                        evidence (stage/refine-argument [:bounded-nat-vector 4096 99] xs)
                        shifted (mapv inc xs)
                        consumer (:consumer ctx) producer (:producer ctx)
                        functions [[:guarded 1 #(stage/with-cache (:cache ctx) (ev/call-value (:closure ctx) [xs]))]
                                   [:evidenced 1 #(pc/consume consumer evidence w/empty-root [])]
                                   [:pure-batch-100 100 #(pc/consume-batch consumer evidence 100 w/empty-root [])]
                                   [:materialize-then-guard 1 #(stage/with-cache (:cache ctx)
                                                              (ev/call-value (:closure ctx) [(mapv inc xs)]))]
                                   [:producer-facts-consumer 1 #(pc/consume consumer (pc/produce producer evidence) w/empty-root [])]
                                   [:scan-producer-consumer 1 #(pc/consume consumer
                                                               (pc/produce producer (stage/refine-argument [:bounded-nat-vector 4096 99] xs))
                                                               w/empty-root [])]]]
                    {:n n :functions functions :expected (bench/primitive xs) :shifted-expected (bench/primitive shifted)}))
                [16 256 4096])
        _ (doseq [{:keys [functions]} cases [label repeats f] functions]
            (dotimes [_ (if (> repeats 1) 100 3000)] (f)))
        rows (mapv
               (fn [{:keys [n functions expected shifted-expected]}]
                 (let [samples (reduce
                                 (fn [out batch]
                                   (reduce (fn [out [label repeats f]]
                                             (let [s (bench/sample (if (> repeats 1) 10 100) f)
                                                   want (if (#{:guarded :evidenced :pure-batch-100} label) expected shifted-expected)]
                                               (assert (= want (:value s)))
                                               (update out label (fnil conj [])
                                                       (assoc s :calls-per-operation repeats :ns-per-call (/ (:ns s) repeats)))))
                                           out (if (even? (+ id batch)) functions (reverse functions)))) {} (range 9))]
                   {:n n :measurements (update-vals samples (fn [ss]
                                                             {:median-ns-per-call (bench/median (map :ns-per-call ss))
                                                              :median-bytes-per-operation (bench/median (map :bytes ss))
                                                              :samples ss}))})) cases)
        paths ["src/klara/stage.clj" "src/klara/compile/staged.clj" "src/klara/compile/infer_affine.clj"
               "src/klara/compile/strict_fold.clj" "experiments/consolidation/checked_pipeline.clj"
               "experiments/consolidation/producer_model.clj" "experiments/consolidation/producer_consumer.clj"]
        report {:process id :java (System/getProperty "java.runtime.version")
                :setup (select-keys ctx [:preparation-ms :publication-ms :legacy-checked-installation-ms :validation-ms])
                :rows rows :guard-profile (profile-guards ctx)
                :source-sha256 (into {} (map (fn [p] [p (c/sha256 (slurp p))]) paths))
                :method {:warmup :all-sizes-before-sampling :calls-per-size 3000 :batch-warmup 100
                         :batches 9 :order :alternating-process-parity :pure-batch-size 100}
                :limitations [:three-process-pilot :one-family :no-cpu-pinning
                              :batch-is-known-pure-driver :producer-output-is-materialized
                              :guard-profile-instrumentation-is-not-additive :facts-bootstrap-excluded-from-warm-evidence-cases]}]
    (spit (str "experiments/consolidation/admission-process-" id ".edn") (with-out-str (pp/pprint report)))
    (println :admission-benchmark-written id)))
(defn -main [id] (run-process! (Long/parseLong id)) (shutdown-agents))

(defn summarize! [ids]
  (let [reports (mapv #(edn/read-string (slurp (str "experiments/consolidation/admission-process-" % ".edn"))) ids)
        summary (fn [xs] {:median (bench/median xs) :min (apply min xs) :max (apply max xs)})
        labels [:guarded :evidenced :pure-batch-100 :materialize-then-guard :producer-facts-consumer :scan-producer-consumer]
        rows (mapv (fn [i]
                     {:n (get-in (first reports) [:rows i :n])
                      :ns-per-call (into {} (for [label labels]
                                             [label (summary (map #(get-in % [:rows i :measurements label :median-ns-per-call]) reports))]))})
                   (range 3))
        phases (into {} (for [key (keys (:setup (first reports)))]
                         [key (summary (map #(get-in % [:setup key]) reports))]))
        result {:processes ids :rows rows :setup-ms phases
                :source-sha256 (:source-sha256 (first reports))
                :method (:method (first reports)) :limitations (:limitations (first reports))
                :all-process-source-hashes-match (apply = (map :source-sha256 reports))}
        cell (fn [row label] (let [{:keys [median min max]} (get-in row [:ns-per-call label])]
                              (format "%.2f [%.2f, %.2f]" (/ median 1000.0) (/ min 1000.0) (/ max 1000.0))))]
    (spit "experiments/consolidation/admission-summary.edn" (with-out-str (pp/pprint result)))
    (spit "experiments/consolidation/admission-summary.md"
          (str "# Producer–consumer admission pilot\n\n"
               "Three sequential JVMs " (pr-str ids) ", Intel Core Ultra 7 258V, no CPU pinning. Times are μs per call: median [min, max] of process medians. Ranges are variability, not confidence intervals. All sizes warm before sampling.\n\n"
               "| n | ordinary guarded | existing value evidence | pure batch of 100, per call | mapv then guarded | checked producer + evidence consumer | input scan + producer + consumer |\n"
               "|---|---|---|---|---|---|---|\n"
               (apply str (for [row rows] (str "| " (:n row) " | " (clojure.string/join " | " (map #(cell row %) labels)) " |\n")))
               "\nThe first three columns consume the same input. The final three consume its incremented elements and include materializing the output vector. Existing-evidence cases exclude the initial scan that creates the evidence; the final column includes it. Batch measurements divide an actual 100-call operation by 100 and include one admission. A batch is an explicit known pure driver, not arbitrary user code with guards removed.\n\n"
               "Setup costs, milliseconds:\n\n```clojure\n" (pr-str phases) "\n```\n\n"
               "Preparation includes prevalidation; publication reuses its receipt. Legacy installation checks again. This moves work out of publication, without claiming the same amount of work vanished. Raw files retain allocation samples and an instrumented guard profile; profile components are not additive timings.\n\n"
               "Processes 0–5 are development diagnostics: 0–1 precede native-worker host-guard repair, 2–4 precede the primitive-return batch ABI, and 5 precedes the final ABI. S28 measurements are historical and do not describe these changes. One workload family and three JVMs remain a pilot.\n"))
    result))
