(ns consolidation.run
  (:require [clojure.test :as test]
            [clojure.pprint :as pp] [clojure.java.io :as io]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [klara.fusion.kernel :as k]
            [klara.core :as core]
            [klara.code-identity-test]
            [consolidation.demand :as demand]
            [consolidation.demand-test]
            [consolidation.demand-model :as demand-model]
            [consolidation.scalar-core :as scalar-core]
            [consolidation.scalar-driver :as scalar-driver]
            [consolidation.scalar-sum :as scalar-sum]
            [consolidation.counted-core :as counted-core]
            [consolidation.scalar-core-test]
            [consolidation.scalar-cek :as scalar-cek] [consolidation.scalar-cek-test]
            [consolidation.scalar-finite :as scalar-finite] [consolidation.scalar-finite-test]
            [consolidation.planning :as planning] [consolidation.planning-test]
            [consolidation.world-evolution :as evolution]
            [klara.deploy :as deploy] [klara.deploy-test]
            [adaptive-affine.predictor-test]
            [klara.compositional-analysis-test]
            [klara.infer-affine-test]
            [klara.snapshot-updates-test]
            [klara.affine-test]
            [klara.staged-compile-test]
            [klara.stage-test]
            [klara.owned-test]
            [klara.deopt-test]
            [consolidation.private-state :as private]
            [consolidation.private-state-test]
            [consolidation.helper-bridge :as helper]
            [consolidation.fold-model :as fold-model]
            [consolidation.native-pipeline-test]
            [consolidation.producer-consumer-test]
            [consolidation.producer-model :as producer-model]
            [consolidation.producer-consumer :as producer-consumer]
            [consolidation.helper-bridge-test]
            [consolidation.source-model-test]
            [consolidation.proved-accumulator-test]
            [consolidation.interval :as interval]
            [consolidation.interval-test]
            [consolidation.checked-pipeline-test]))

(def ^:dynamic *output-directory* "target/verification")
(defn artifact-path [name]
  (let [path (str *output-directory* "/" name)] (io/make-parents path) path))

(defn export-native-example! []
  (let [request (first (consolidation.native-pipeline-test/requests))
        candidate (consolidation.checked-pipeline/prepare klara.world/empty-root request)
        exe (.-executable ^klara.compile.staged.Prepared candidate)
        native (:native-executable exe)
        artifact {:source (:generic exe) :mathematical-target (:target exe)
                  :lowered-functional (:generic native)
                  :normalized-functional (get-in native [:inference :analysis :term])
                  :owned (get-in native [:inference :owned])
                  :ownership-derivation (get-in native [:inference :derivation])
                  :entry-guards (mapv #(if (= :host-root (first %)) [(first %) (second %) :reference-root] %) (:guards exe))
                  :lowering (:lowering exe)
                  :private-witness (assoc (select-keys (:private-witness exe)
                                                     [:source-id :target-id :goal-sha256 :proof-sha256])
                                         :goal (str (get-in exe [:private-witness :goal])))
                  :implementation-bridges :tested}
        text (with-out-str (pp/pprint artifact))
        path (artifact-path "native-example.edn")]
    (spit path text)
    {:path path :sha256 (core/sha256 text)}))

(defn export-producer-example! []
  (let [source (klara.infer-affine-test/source '(fn [x] (+ x 1)))
        producer (producer-consumer/prepare-producer source 99)
        info (producer-consumer/producer-info producer)
        proof (.-witness ^consolidation.producer_consumer.Producer producer)
        input (klara.stage/refine-argument [:bounded-nat-vector 64 99] [1 2 3])
        output (producer-consumer/produce producer input)
        artifact {:source (klara.infer-affine-test/term source) :contract info
                  :goal (str (:goal proof))
                  :input-fact (klara.stage/evidence-info input)
                  :output-fact (klara.stage/evidence-info output)
                  :output-value (klara.stage/evidence-value output)
                  :bridges :tested-producer-driver-and-core-JVM-correspondence}
        text (with-out-str (pp/pprint artifact)) path (artifact-path "producer-example.edn")]
    (spit path text) {:path path :sha256 (core/sha256 text)}))

(defn export-demand-example! []
  (let [request (consolidation.demand-test/request
                  (klara.infer-affine-test/source '(fn [x] (+ x 1)))
                  3 {:max-count 64 :max-x 10} 'map)
        candidate (demand/prepare klara.world/empty-root request)
        exe (.-executable ^klara.compile.staged.Prepared candidate)
        native (:native-executable exe)
        artifact {:canonical-version 1 :source (:generic exe) :target (:target exe)
                  :lowered-functional (:generic native)
                  :owned (get-in native [:inference :owned])
                  :contract (:demand (.-info ^klara.compile.staged.Prepared candidate))
                  :witness (assoc (select-keys (:witness exe) [:goal-sha256 :proof-sha256])
                                  :goal (str (get-in exe [:witness :goal])))
                  :bridges :tested-Core-model-and-JVM-correspondence
                  :suspension :T0-between-completed-native-regions}
        output (with-out-str (pp/pprint artifact))
        path (artifact-path "demand-example.edn")]
    (spit path output) {:path path :sha256 (core/sha256 output)}))

(defn export-suspension-trace! []
  (let [world (consolidation.demand-test/example-world)
        old (klara.world/snapshot world)
        cache (klara.stage/make-cache) store (klara.authority/new-store)
        artifact
        (binding [klara.authority/*store* store]
          (klara.stage/with-cache cache
            (let [installed (klara.defs/eval-form old '(refine-prefix prefix-request))]
              (klara.defs/define! world '(def saved-task (start-prefix-task [1 2 3 4])))
              (let [task (klara.defs/lookup (klara.world/snapshot world) 'saved-task)]
                (klara.defs/define! world '(def calibration 100))
                (let [new (klara.world/snapshot world)
                      result (klara.defs/eval-form new '(resume-prefix-task saved-task 5))
                      second-resume (try
                                      (klara.defs/eval-form new '(resume-prefix-task saved-task 5))
                                      :unexpected-success
                                      (catch Throwable _ :rejected))]
                  {:installation (:status installed)
                   :suspended (select-keys task [:status :request])
                   :new-world-calibration (klara.defs/lookup new 'calibration)
                   :resumed result
                   :lease-status (:status (klara.authority/state (:lease task)))
                   :second-resume second-resume
                   :native-hits (:hits (klara.stage/stats cache))
                   :scope :lexical-T0-await-between-native-regions
                   :evidence :tested-operational-trace})))))]
    (when-not (and (= {:value 33 :calibration 10} (:resumed artifact))
                   (= :settled (:lease-status artifact))
                   (= :rejected (:second-resume artifact))
                   (>= (:native-hits artifact) 2))
      (throw (ex-info "suspension trace failed" artifact)))
    (let [output (with-out-str (pp/pprint artifact))
          path (artifact-path "suspension-trace.edn")]
      (spit path output) {:path path :sha256 (core/sha256 output)})))

(defn export-correspondence-example! []
  (let [body (nth consolidation.scalar-core-test/bodies 2)
        source (consolidation.scalar-core-test/fold-source body 0 3)
        target (:target (klara.compile.strict-fold/lower source))
        receipt (counted-core/witness source target [100 10])
        scalar (:scalar-witness receipt)
        sum-source (consolidation.scalar-core-test/fold-source (first consolidation.scalar-core-test/bodies) 0 3)
        sum-target (:target (klara.compile.strict-fold/lower sum-source))
        sum (counted-core/sum-witness sum-source sum-target 64 10)
        artifact {:source source :counted-target target
                  :scalar (assoc (select-keys scalar [:input-bounds :upper :capacity :source-id :goal-sha256 :proof-sha256 :bridges])
                                 :checked-goal (str (:checked-goal scalar)))
                  :driver (assoc (select-keys receipt [:source-id :target-id :goal-sha256 :proof-sha256
                                                       :checked-goal-sha256 :checked-proof-sha256 :bridges :reachable-safety-premise])
                                 :checked-goal (str (:checked-goal receipt)))
                  :sum {:source sum-source :counted-target sum-target
                        :contract (select-keys sum [:source-id :target-id :max-count :max-x :invariant
                                                     :reachable-safety-premise :goal-sha256 :proof-sha256 :bridges])
                        :goal (str (:goal sum))}
                  :not-established [:full-Core-CEK-adequacy :arbitrary-loop-invariant-inference :verified-JVM-emission]}
        output (with-out-str (pp/pprint artifact))
        path (artifact-path "correspondence-example.edn")]
    (spit path output) {:path path :sha256 (core/sha256 output)}))

(defn export-live-planning! []
  (let [world (planning/load-world) root (klara.world/snapshot world)
        problem (planning/problem [1 2 3] {:max-count 64 :max-x 10})
        limits {:search-fuel 16 :transition-fuel 100000}
        cache (klara.stage/make-cache)
        short (planning/invest cache klara.world/empty-root root 'plan-optimizer problem
                               {:remaining-calls 0} limits (planning/controller 10000000000 3))
        hot (planning/invest cache klara.world/empty-root root 'plan-optimizer problem
                             {:remaining-calls 10000} limits (:controller short))
        bad (planning/prepare-plan klara.world/empty-root problem (assoc-in (:plan hot) [:steps 0 :coefficients] [1 2 4]))
        result (klara.stage/with-cache cache (proof-staging/run-code (get-in problem [:codes :source]) [1 2 3]))
        state {:problem problem :profile {:remaining-calls 10000} :controller (:controller hot)}
        bundle (deploy/freeze root state)
        bundle-path (deploy/store! (str *output-directory* "/deployment") bundle)
        restored (deploy/load! bundle-path)
        restored-plan (planning/invoke-policy (klara.world/snapshot (:world restored)) 'plan-optimizer
                                             [(get-in restored [:state :problem]) {:remaining-calls 10000}
                                              {:search-fuel 16 :preparation-ns 1000000000}] 100000)
        artifact {:policy-source (:form (klara.world/entry* root 'plan-optimizer))
                  :estimates (:estimates problem) :estimate-provenance (:estimate-provenance problem)
                  :short-status (:status short) :hot-status (:status hot)
                  :plan (select-keys (:plan hot) [:node :steps :target-ids :executor :expanded :expected-benefit])
                  :work (get-in hot [:controller :history])
                  :bad-proposal (select-keys bad [:status :reason :elapsed-ns])
                  :result result :world-evolution (evolution/run-experiment!)
                  :deployment {:path bundle-path :id (:id bundle) :restored-plan-node (get-in restored-plan [:value :node])
                               :empty-cache (empty? (klara.stage/executables (:cache restored)))}
                  :timing-scope :single-process-diagnostic-not-performance-evaluation}]
    (when-not (and (= :stopped (:status short)) (= :installed (:status hot))
                   (= :declined (:status bad)) (= 57 result) (= :both (get-in restored-plan [:value :node])))
      (throw (ex-info "live planning artifact failed" (dissoc artifact :policy-source))))
    (let [output (with-out-str (pp/pprint artifact)) path (artifact-path "live-planning.edn")]
      (spit path output) {:path path :sha256 (core/sha256 output)})))

(defn export-CEK-example! []
  (let [body (nth consolidation.scalar-core-test/bodies 2)
        receipt (scalar-cek/execution-witness body [10 10])
        finite-receipt (scalar-finite/execution-witness body 2)
        artifact {:source body :input-bounds [10 10]
                  :finite-environment-receipt (select-keys finite-receipt [:source-id :goal-sha256 :proof-sha256 :bridges])
                  :receipt (assoc (select-keys receipt [:source-id :goal-sha256 :proof-sha256 :bridges]) :goal (str (:goal receipt)))
                  :example (scalar-cek/observe body [7 3] Long/MAX_VALUE (scalar-cek/step-bound body))
                  :model :restricted-defunctionalized-scalar-CEK}
        output (with-out-str (pp/pprint artifact)) path (artifact-path "scalar-cek.edn")]
    (spit path output) {:path path :sha256 (core/sha256 output)}))

(defn theorem-receipt [en name]
  (let [d (env/lookup en (nm/from-string name))
        goal (env/ci-type d) proof (env/ci-value d)]
    {:name name :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)
     :kernel-accepted (env/verifies? en goal proof)
     :self-reference (contains? (k/constants-of proof) name)}))

(defn- verify-run! []
  (let [result (test/run-tests 'klara.compositional-analysis-test 'klara.infer-affine-test
                               'klara.affine-test 'klara.staged-compile-test
                               'klara.stage-test 'klara.owned-test 'klara.deopt-test
                               'consolidation.private-state-test 'consolidation.interval-test
                               'consolidation.checked-pipeline-test
                               'consolidation.helper-bridge-test 'consolidation.source-model-test
                               'consolidation.proved-accumulator-test
                               'klara.snapshot-updates-test 'consolidation.native-pipeline-test
                               'consolidation.producer-consumer-test
                               'klara.code-identity-test 'consolidation.demand-test
                               'consolidation.scalar-core-test 'consolidation.scalar-cek-test 'consolidation.scalar-finite-test
                               'consolidation.planning-test 'klara.deploy-test
                               'adaptive-affine.predictor-test)
        pe (:environment @private/proof-state) be @interval/proof-state he @helper/proof-state fe @fold-model/proof-state
        report {:java (System/getProperty "java.runtime.version")
                :native-example (export-native-example!)
                :producer-example (export-producer-example!)
                :demand-example (export-demand-example!)
                :suspension-trace (export-suspension-trace!)
                :canonical-version 1
                :correspondence-example (export-correspondence-example!)
                :scalar-cek-example (export-CEK-example!)
                :live-planning-example (export-live-planning!)
                :ansatz-dependency "0.2.115" :tests result
                :source-sha256
                (into {} (map (fn [path] [path (core/sha256 (slurp path))]))
                      ["src/klara/core.clj" "src/klara/world.clj" "src/klara/defs.clj"
                       "src/klara/syntax.clj" "src/klara/expand.clj"
                       "src/klara/eval.clj" "src/klara/deploy.clj" "src/klara/fusion.clj"
                       "src/klara/compile/requirements.clj" "src/klara/compile/analysis.clj" "src/klara/compile/infer_affine.clj"
                       "src/klara/compile/affine_erase.clj" "src/klara/stage.clj"
                       "src/klara/compile/updates.clj" "src/klara/compile/strict_fold.clj"
                       "experiments/proof_staging/proof_staging.clj"
                       "experiments/consolidation/private_state.clj"
                       "experiments/consolidation/interval.clj"
                       "experiments/consolidation/checked_pipeline.clj"
                       "experiments/consolidation/helper_bridge.clj"
                       "experiments/consolidation/source_model.clj"
                       "experiments/consolidation/proved_accumulator.clj"
                       "experiments/consolidation/fold_model.clj"
                       "src/klara/compile/staged.clj"
                       "experiments/consolidation/producer_model.clj"
                       "experiments/consolidation/producer_consumer.clj"
                       "experiments/consolidation/demand.clj"
                       "experiments/consolidation/demand_model.clj"
                       "experiments/consolidation/demand_test.clj"
                       "test/klara/code_identity_test.clj"
                       "experiments/consolidation/run.clj"
                       "experiments/consolidation/scalar_core.clj"
                       "experiments/consolidation/scalar_driver.clj"
                       "experiments/consolidation/scalar_sum.clj"
                       "experiments/consolidation/counted_core.clj"
                       "experiments/consolidation/scalar_core_test.clj"
                       "experiments/consolidation/scalar_cek.clj"
                       "experiments/consolidation/scalar_cek_test.clj"
                       "experiments/consolidation/scalar_finite.clj"
                       "experiments/consolidation/scalar_finite_test.clj"
                       "experiments/consolidation/planning.clj"
                       "experiments/consolidation/planning_test.clj"
                       "experiments/adaptive_affine/bench.clj"
                       "experiments/adaptive_affine/predictor.clj"
                       "experiments/adaptive_affine/predictor_test.clj"
                       "examples/staging/15-planned-jit.klr"
                       "examples/staging/14-demand-and-await.klr"])
                :private-theorems
                (mapv #(theorem-receipt pe %)
                      ["private-state-simulation" "private-retain-rejected"
                       "private-branch-requires-both" "private-repeat-safe"])
                :bounds-theorems
                (mapv #(theorem-receipt be %)
                      ["bound-monotone" "bound-value-safe" "bound-fits-sound" "bound-checked-sound"])
                :helper-theorems
                (mapv #(theorem-receipt he %)
                      ["helper-loop-substitution" "helper-reference-private"
                       "helper-private-composition" "helper-counter-index-safe"])
                :fold-theorems
                (mapv #(theorem-receipt fe %)
                      ["fold-step-refinement" "fold-private-refinement" "fold-total-source" "fold-sum-bound"])
                :numeric-context-theorems
                (mapv #(theorem-receipt fe %)
                      ["KlaraExperiment.horner-fold-step" "KlaraExperiment.horner-fold-sum"])
                :producer-theorems
                (mapv #(theorem-receipt @producer-model/proof-state %)
                      ["producer-bound-weaken" "producer-map-bound"])
                :demand-theorems
                (mapv #(theorem-receipt @demand-model/proof-state %)
                      ["demand-take-map" "demand-zero-elements"
                       "demand-prefix-ignores-tail" "demand-spin-pending"])
                :scalar-core-theorems (mapv #(theorem-receipt @scalar-core/proof-state %) scalar-core/theorem-names)
                :scalar-driver-theorems (mapv #(theorem-receipt @scalar-driver/proof-state %) scalar-driver/theorem-names)
                :scalar-sum-theorems (mapv #(theorem-receipt @scalar-sum/proof-state %) scalar-sum/theorem-names)
                :scalar-cek-theorems (mapv #(theorem-receipt @scalar-cek/proof-state %) scalar-cek/theorem-names)
                :scalar-finite-theorems (mapv #(theorem-receipt @scalar-finite/proof-state %) scalar-finite/theorem-names)
                :trust [:bundled-init-statements :core-model-elaboration :T0-correspondence
                        :Clojure-JVM-backend :tested-owned-erasure]
                :not-established [:whole-compiler-correctness :full-summary-soundness
                                  :general-scope-freshness :fully-proved-native-chain
                                  :interior-owned-recovery :publication-quality-performance]}]
    (doseq [receipt (mapcat report [:private-theorems :bounds-theorems :helper-theorems :fold-theorems :numeric-context-theorems :producer-theorems :demand-theorems
                                  :scalar-core-theorems :scalar-driver-theorems :scalar-sum-theorems :scalar-cek-theorems :scalar-finite-theorems])]
      (when-not (and (:kernel-accepted receipt) (not (:self-reference receipt)))
        (throw (ex-info "invalid exported theorem receipt" receipt))))
    (spit (artifact-path "evidence.edn") (with-out-str (pp/pprint report)))
    report))


(defn verify!
  ([] (verify! "target/verification"))
  ([output-directory]
   (binding [*output-directory* output-directory] (verify-run!))))

(defn -main [& [output-directory]]
  (let [report (verify! (or output-directory "target/verification"))
        result (:tests report)]
    (println :verification result)
    (shutdown-agents)
    (System/exit (+ (:fail result) (:error result)))))
