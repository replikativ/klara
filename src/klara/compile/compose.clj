(ns klara.compile.compose
  "Bounded driver for hosted adapters to independently checked recipes.
   Chaining receipts does not establish the correctness of an arbitrary step."
  (:require [klara.compile.budget :as budget] [klara.core :as core]
            [klara.compile.edge :as edge] [klara.compile.subject :as subject]))

(def default-rounds 2)
(def maximum-rounds 4)

(defn rounds! [rounds]
  (when-not (and (integer? rounds) (<= 1 rounds maximum-rounds))
    (throw (ex-info "invalid rewrite round allowance" {:reason :invalid-rewrite-rounds})))
  rounds)

(defn- reject! [check]
  (throw (ex-info "checked recipe chain rejected" {:reason :recipe-chain :check check})))

(defn drive
  "Controller for trusted adapters to checked recipes or read-only inspection.
   Guest decisions are inert data; only the adapter can issue accepted edges."
  [b source advance validate steps]
  (when-not (and (integer? steps) (<= 1 steps 8))
    (throw (ex-info "invalid strategy allowance" {:reason :invalid-strategy-steps})))
  (loop [term source round 0 receipts [] edges [] history [] reads #{} calls 0 seen #{}]
    (budget/charge! b :work 1)
    (if (= round steps)
      {:term term :receipts receipts :edges edges :history history :compiler-reads reads :calls-inlined calls
       :rounds round :stop :round-limit}
      (let [source-id (core/code-id term)
            result (advance {:term term :history history :round round})
            target (:term result) accepted (:edge result)
            _ (when-not (map? target) (reject! :missing-residual))
            ;; Bounds precede hashing/printing or analyzing newly expanded data.
            _ (validate target)
            target-id (core/code-id target)
            changed? (not= source-id target-id)
            _ (when (and changed? (not (edge/checked? accepted))) (reject! :unchecked-edge))
            _ (when (and accepted (not (edge/connects? accepted term target subject/core-contract)))
                (reject! :source-or-target))
            receipt (when accepted (edge/info accepted))
            _ (when (and (:receipt result) (not= receipt (:receipt result)))
                (reject! :diagnostic-mismatch))
            _ (when (and (seq receipts) (not= source-id (:target-id (peek receipts))))
                (reject! :disconnected))
            _ (when (and changed? (contains? seen target-id)) (reject! :cycle))
            receipts (cond-> receipts receipt (conj receipt))
            edges (cond-> edges accepted (conj accepted))
            history (conj history (merge {:source-id source-id :target-id target-id :changed? changed?}
                                         (:history result)))
            reads (into reads (:compiler-reads result))
            calls (+ calls (or (:calls-inlined result) 0))]
        (if (and (not (:done? result)) (or changed? (:continue? result)))
          (recur target (inc round) receipts edges history reads calls
                 (cond-> seen changed? (conj source-id)))
          {:term target :receipts receipts :edges edges :history history :compiler-reads reads :calls-inlined calls
           :endpoint (:endpoint result)
           :rounds (inc round) :stop (if (:done? result) :finished :fixed-point)})))))

(defn run
  "Compatibility adapter: repeat the checked local recipe with fresh analysis."
  [b source step validate rounds]
  (rounds! rounds)
  (drive b source #(step (:term %)) validate rounds))
