(ns klara.compile.strategy
  "Source-backed bounded guest strategy over checked adapters. Decision data
   cannot supply a checker, arbitrary replacement IR, or a weaker contract."
  (:require [klara.compile.budget :as budget] [klara.compile.compose :as compose]
            [klara.compile.ir :as ir] [klara.compile.local-calls :as local]
            [klara.compile.service :as service] [klara.compile.subject :as subject]
            [klara.compile.diagnostics :as diagnostics]
            [klara.core :as core]))

(def default-steps 4)
(defn steps! [n]
  (when-not (and (integer? n) (<= 1 n 8))
    (throw (ex-info "invalid strategy allowance" {:reason :invalid-strategy-steps}))) n)

(defn- inspect [b term]
  (let [nodes (reduce (fn [n _] (budget/charge! b :work 1) (inc n)) 0 (ir/nodes term))]
    {:source-id (core/code-id term) :nodes (long nodes)
     :local-functions (long (count (filter #(and (= :let (:op %)) (= :fn (get-in % [:init :op])))
                                         (ir/nodes term))))}))

(defn run
  ([b policy-root term strategy validate steps] (run b policy-root term strategy validate steps {}))
  ([b policy-root term strategy validate steps options]
  (steps! steps)
  (when-not (symbol? strategy)
    (throw (ex-info "strategy must name a world function" {:reason :invalid-strategy})))
  (compose/drive b term
    (fn [{:keys [term history round]}]
      (let [description (inspect b term)
            request {:source description :contract subject/core-contract
                     :history history :remaining (long (- steps round))}
            decision (service/invoke b policy-root strategy [request] 4096)
            action (:value decision)
            _ (when-not (and (map? action)
                             (case (:action action)
                               :inspect (= #{:action} (set (keys action)))
                               :finish (= #{:action} (set (keys action)))
                               :private-accumulator (= #{:action} (set (keys action)))
                               :local-call (and (= #{:action :planner} (set (keys action)))
                                                (symbol? (:planner action))) false))
                (throw (ex-info "invalid compiler strategy action" {:reason :invalid-strategy-action})))
            result (case (:action action)
                     :local-call (local/run b policy-root term (:planner action))
                     :private-accumulator
                     {:term term :calls-inlined 0 :compiler-reads #{}
                      :endpoint (let [prepare (diagnostics/phase :backend-initialization {:backend :private-accumulator}
                                                (requiring-resolve 'klara.compile.private-accumulator/plan))]
                                  (prepare b term options))}
                     {:term term :calls-inlined 0 :compiler-reads #{}})]
        (assoc result :continue? true :done? (contains? #{:finish :private-accumulator} (:action action))
               :compiler-reads (into (:compiler-reads decision) (:compiler-reads result))
               :history (cond-> {:action (:action action)
                                :strategy-transitions (long (:transitions decision))}
                          (= :inspect (:action action)) (assoc :inspection description)))))
    validate steps)))
