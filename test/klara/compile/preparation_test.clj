(ns klara.compile.preparation-test
  (:require [clojure.test :refer [deftest is]] [klara.affine :as affine]
            [klara.code :as code] [klara.compile.affine-erase :as erase]
            [klara.compile.budget :as budget] [klara.compile.diagnostics :as diagnostics]
            [klara.compile.funding :as funding] [klara.compile.infer-affine :as inference]
            [klara.compile.ir :as ir] [klara.compile.local-calls :as local]
            [klara.compile.private-accumulator :as private]
            [klara.compile.support :as fixture]
            [klara.compile.staged :as staged] [klara.defs :as defs]
            [klara.stage :as stage] [klara.world :as world]))

(defn input []
  (let [w (fixture/setup fixture/source) root (world/snapshot w)
        code (defs/eval-form root (list 'code fixture/source))]
    {:root root :code code :term (:term (local/run (budget/budget) root
                                        (ir/lower (ir/named (code/s->core (code/code-term code)))) local/planner-symbol))}))

(deftest analysis-once-and-repeat-control-have-the-same-checked-endpoint
  (let [{:keys [term]} (input)
        once (diagnostics/capture #(private/plan (budget/budget) term))
        repeated (diagnostics/capture #(private/plan (budget/budget) term {:repeat-private-analysis? true}))
        phases #(frequencies (map :phase (get-in % [:diagnostics :events])))]
    (is (= (private/target (:value once)) (private/target (:value repeated))))
    (is (= 1 (:private-analysis (phases once))))
    (is (= 2 (:private-analysis (phases repeated))))
    (is (= 1 (:private-analysis-check (phases once)) (:private-analysis-check (phases repeated))))
    (is (= 1 (:ownership-verify (phases once)) (:ownership-verify (phases repeated))))))

(deftest candidate-local-artifact-binds-source-consumer-layout-and-derivation
  (let [{:keys [term]} (input)
        analyze (ns-resolve 'klara.compile.private-accumulator 'analyze)
        artifact (analyze (budget/budget) term)]
    (is (identical? artifact (private/check-analysis! (budget/budget) term artifact)))
    (doseq [bad [(assoc artifact :source (into {} term))
                 (assoc-in artifact [:loop-source :arity] 0)
                 (assoc-in artifact [:inference :source-id] "wrong-source")
                 (assoc-in artifact [:owned :body :init] {:op :quote :datum nil})
                 (assoc-in artifact [:owned :body :body] {:op :quote :datum true})
                 (assoc artifact :guards #{})
                 (assoc-in artifact [:info :length] 99)
                 (assoc-in artifact [:info :parameter-layouts] [:any :any :any])
                 (assoc-in artifact [:info :kernel-proof-attached?] true)
                 (assoc-in artifact [:derivation :code-id] "wrong-owned")]]
      (is (thrown? clojure.lang.ExceptionInfo (private/check-analysis! (budget/budget) term bad))))))

(deftest later-jobs-produce-and-check-their-own-artifacts
  (let [{:keys [term root code]} (input) calls (atom 0) infer inference/infer]
    (with-redefs [inference/infer (fn [& args] (swap! calls inc) (apply infer args))]
      (let [first (private/plan (budget/budget) term) second (private/plan (budget/budget) term)]
        (is (= 2 @calls))
        (is (not (identical? first second)))
        (is (= (private/target first) (private/target second)))))
    (with-redefs [private/check-analysis! (fn [& _] (throw (ex-info "changed checker" {:reason :private-analysis :check :changed}))) ]
      (let [r (staged/request root code {:job (funding/create {}) :strategy 'strategy})]
        (is (= :rejected (:status r)))
        (is (nil? (:candidate r)))))))

(deftest validation-still-runs-erasure-and-rejects-stale-registry-receipts
  (let [{:keys [root code]} (input)
        p (:candidate (staged/request root code {:job (funding/create {}) :strategy 'strategy}))
        captured (diagnostics/capture #(staged/prevalidate p))
        phases (get-in captured [:diagnostics :events])]
    (is (= 1 (count (filter #(and (= :owned-erasure (:phase %))
                                  (= :validation (get-in % [:details :use]))) phases))))
    ;; A changed trusted helper is actually invoked; no cached verdict bypasses it.
    (with-redefs [erase/erase (fn [& _] (throw (ex-info "changed erasure helper" {:test :helper-change}))) ]
      (is (thrown? clojure.lang.ExceptionInfo (staged/prevalidate p))))
    (let [registry (var-get (ns-resolve 'klara.stage 'checkers)) old @registry
          cache (stage/make-cache)]
      (try
        (stage/register-checker! ::unrelated (constantly nil))
        (is (= :checker-registry-changed
               (try (staged/install! cache root (:value captured)) nil
                    (catch clojure.lang.ExceptionInfo e (:reason (ex-data e))))))
        (is (empty? (stage/executables cache)))
        (is (= :installed (:status (staged/install! cache root (staged/prevalidate p)))))
        (finally (reset! registry old))))))

(deftest preparation-diagnostics-are-bounded-and-record-failure
  (let [events (atom {:events [] :dropped 0}) calls (atom 0)]
    (binding [diagnostics/*events* events]
      (dotimes [_ (+ 3 diagnostics/maximum-events)]
        (diagnostics/phase :probe {} (swap! calls inc)))
      (is (thrown? clojure.lang.ExceptionInfo
                   (diagnostics/phase :failure {} (throw (ex-info "probe" {}))))))
    (is (= (+ 3 diagnostics/maximum-events) @calls))
    (is (= diagnostics/maximum-events (count (:events @events))))
    (is (= 4 (:dropped @events))))
  (let [events (atom {:events [] :dropped 0})]
    (binding [diagnostics/*events* events]
      (try (diagnostics/phase :failure {} (throw (ex-info "probe" {}))) (catch Exception _)))
    (is (= :failed (get-in @events [:events 0 :status])))))
