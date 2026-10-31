(ns consolidation.stage-world-bindings
  "Diagnostic for lexical staging versus persistent global binding semantics.
   Checks the narrow supported/rejected boundary; no universal linking theorem."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.code :as code] [klara.core :as core] [klara.defs :as defs]
            [klara.eval :as ev] [klara.world :as world]))

(defn run-probe! []
  (let [w (world/make-world)
        _ (doseq [form ['(def setting 10)
                        '(def late (code (+ setting 1)))
                        '(def frozen (let [value setting] (code (+ value 1))))
                        '(def reader (fn [] setting))]]
            (defs/define! w form))
        old (world/snapshot w) frozen (defs/lookup old 'frozen)
        reader (defs/lookup old 'reader)
        lifting (try (ev/lift-term reader) :unexpectedly-accepted
                     (catch clojure.lang.ExceptionInfo e {:rejected (.getMessage e)}))
        _ (defs/define! w '(def setting 20)) now (world/snapshot w)
        run-code (fn [root c] (ev/run (code/s->core (code/code-term c)) {:basis root}))
        original (ev/call-value reader [])
        report {:scope :conservative-pinned-lifting-boundary
                :late-global {:old-result (defs/eval-form old '(run late))
                              :new-result (defs/eval-form now '(run late))
                              :definition-pending? (world/pending? now (world/entry* now 'late))
                              :reads (:reads (world/entry* now 'late))}
                :early-value {:saved-code-result (run-code now frozen)
                              :definition-pending? (world/pending? now (world/entry* now 'frozen))
                              :reads (:reads (world/entry* now 'frozen))}
                :lifted-pinned-closure {:original-result original :lifting lifting}
                :contract :reject-unsupported-crossings-preserve-supported-bindings
                :limits [:no-general-stage-binding-specification
                         :no-claim-of-universal-lift-correctness]
                :source-sha256 (into {} (for [p ["src/klara/defs.clj" "src/klara/world.clj"
                                                "src/klara/eval.clj" "src/klara/code.clj"
                                                "src/klara/expand.clj"
                                                "experiments/consolidation/stage_world_bindings.clj"]]
                                         [p (core/sha256 (slurp p))]))}
        path "target/stage-world-bindings/results.edn"]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report))) report))

(defn -main [& _] (pp/pprint (run-probe!)) (shutdown-agents))
