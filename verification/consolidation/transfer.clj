(ns consolidation.transfer
  "Universal ordered transfer model with explicit errors and pure commit.
   A structural adapter binds the actual compiler plan; expression evaluation,
   named binding and Java lowering remain separate implementation bridges."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e] [klara.fusion.kernel :as k]
            [klara.compile.loop :as loop] [klara.core :as core]))

(def theorem-names ["transfer-dispatch-prepend" "transfer-head-refines" "transfer-refines"
                    "transfer-evaluators-refine" "transfer-failure" "transfer-success"])

(defn- build! []
 (binding [*ns* (the-ns 'consolidation.transfer)]
 (reset! a/ansatz-env (k/env*))
(a/inductive TransferResult [V Type E Type] (ok [value V]) (error [code E]))
(a/inductive TransferExit [V Type E Type]
  (done [values (List V)]) (failed [code E] [old (List V)]))
(a/defn transferPrepend [V :- Type, E :- Type, value :- V, answer :- (TransferResult (List V) E)] (TransferResult (List V) E)
  (match answer
    [(ok values) (TransferResult.ok (List V) E (List.cons V value values))]
    [(error code) (TransferResult.error (List V) E code)]))
(a/defn transferSource [V :- Type, E :- Type, X :- Type, xs :- (List X)]
  (=> (=> X (TransferResult V E)) (TransferResult (List V) E))
  (match xs
    [nil (fn [evaluate :- (=> X (TransferResult V E))]
           (TransferResult.ok (List V) E (List.nil V)))]
    [(cons head tail) (fn [evaluate :- (=> X (TransferResult V E))]
                       (match (evaluate head)
                         [(error code) (TransferResult.error (List V) E code)]
                         [(ok value) (transferPrepend V E value (transferSource V E X tail evaluate))]))]))
(a/defn transferDispatch [V :- Type, E :- Type, old :- (List V), answer :- (TransferResult (List V) E),
                         commit :- (=> (List V) (TransferExit V E))] (TransferExit V E)
  (match answer [(error code) (TransferExit.failed V E code old)] [(ok values) (commit values)]))
(a/defn transferTarget [V :- Type, E :- Type, X :- Type, xs :- (List X)]
  (=> (=> X (TransferResult V E)) (=> (List V) (=> (=> (List V) (TransferExit V E)) (TransferExit V E))))
  (match xs
    [nil (fn [evaluate :- (=> X (TransferResult V E)), old :- (List V), commit :- (=> (List V) (TransferExit V E))]
           (commit (List.nil V)))]
    [(cons head tail)
     (fn [evaluate :- (=> X (TransferResult V E)), old :- (List V), commit :- (=> (List V) (TransferExit V E))]
       (match (evaluate head)
         [(error code) (TransferExit.failed V E code old)]
         [(ok value) (transferTarget V E X tail evaluate old
                       (fn [values :- (List V)] (commit (List.cons V value values))))]))]))
(a/theorem transfer-dispatch-prepend
 [V :- Type, E :- Type, value :- V, answer :- (TransferResult (List V) E), old :- (List V),
  commit :- (=> (List V) (TransferExit V E))]
 (= (TransferExit V E)
    (transferDispatch V E old (transferPrepend V E value answer) commit)
    (transferDispatch V E old answer (fn [values :- (List V)] (commit (List.cons V value values)))))
 (cases answer) (all_goals (rfl)))
(a/defn transferSourceHead [V :- Type, E :- Type, answer :- (TransferResult V E), tail :- (TransferResult (List V) E)]
  (TransferResult (List V) E)
  (match answer [(error code) (TransferResult.error (List V) E code)]
                [(ok value) (transferPrepend V E value tail)]))
(a/defn transferTargetHead [V :- Type, E :- Type, answer :- (TransferResult V E),
                          old :- (List V), tail :- (=> (=> (List V) (TransferExit V E)) (TransferExit V E)),
                          commit :- (=> (List V) (TransferExit V E))] (TransferExit V E)
  (match answer [(error code) (TransferExit.failed V E code old)]
                [(ok value) (tail (fn [values :- (List V)] (commit (List.cons V value values))))]))
(a/theorem transfer-head-refines
 [V :- Type, E :- Type, answer :- (TransferResult V E), sourceTail :- (TransferResult (List V) E),
  old :- (List V), targetTail :- (=> (=> (List V) (TransferExit V E)) (TransferExit V E)),
  h :- (forall [commit :- (=> (List V) (TransferExit V E))]
        (= (TransferExit V E) (targetTail commit) (transferDispatch V E old sourceTail commit))),
  commit :- (=> (List V) (TransferExit V E))]
 (= (TransferExit V E) (transferTargetHead V E answer old targetTail commit)
    (transferDispatch V E old (transferSourceHead V E answer sourceTail) commit))
 (cases answer) (all_goals (try (rfl)))
 (exact (Eq.trans (h (fn [values :- (List V)] (commit (List.cons V value values))))
                  (Eq.symm (transfer-dispatch-prepend V E value sourceTail old commit)))))
(a/theorem transfer-refines
 [V :- Type, E :- Type, X :- Type, xs :- (List X)]
 (forall [evaluate :- (=> X (TransferResult V E)), old :- (List V), commit :- (=> (List V) (TransferExit V E))]
  (= (TransferExit V E) (transferTarget V E X xs evaluate old commit)
      (transferDispatch V E old (transferSource V E X xs evaluate) commit)))
 (induction xs)
 (all_goals (intro evaluate) (intro old) (intro commit))
 (all_goals (try (rfl)))
 (exact (transfer-head-refines V E (evaluate head) (transferSource V E X tail evaluate) old
           (fn [next :- (=> (List V) (TransferExit V E))] (transferTarget V E X tail evaluate old next))
           (ih_tail evaluate old) commit)))

(a/theorem transfer-evaluators-refine
 [V :- Type, E :- Type, X :- Type, xs :- (List X),
  source :- (=> X (TransferResult V E)), target :- (=> X (TransferResult V E)),
  agreement :- (forall [x :- X] (= (TransferResult V E) (target x) (source x))),
  old :- (List V), commit :- (=> (List V) (TransferExit V E))]
 (= (TransferExit V E) (transferTarget V E X xs target old commit)
                      (transferDispatch V E old (transferSource V E X xs source) commit))
 (exact (Eq.trans (transfer-refines V E X xs target old commit)
          (congrArg (fn [evaluate :- (=> X (TransferResult V E))]
                      (transferDispatch V E old (transferSource V E X xs evaluate) commit))
                    (funext agreement)))))
(a/theorem transfer-failure
 [V :- Type, E :- Type, X :- Type, xs :- (List X), evaluate :- (=> X (TransferResult V E)),
  old :- (List V), code :- E,
  failed :- (= (TransferResult (List V) E) (transferSource V E X xs evaluate)
                                        (TransferResult.error (List V) E code))]
 (= (TransferExit V E) (transferTarget V E X xs evaluate old (fn [next :- (List V)] (TransferExit.done V E next)))
                      (TransferExit.failed V E code old))
 (exact (Eq.trans (transfer-refines V E X xs evaluate old (fn [next :- (List V)] (TransferExit.done V E next)))
          (congrArg (fn [answer :- (TransferResult (List V) E)]
                      (transferDispatch V E old answer (fn [next :- (List V)] (TransferExit.done V E next)))) failed))))
(a/theorem transfer-success
 [V :- Type, E :- Type, X :- Type, xs :- (List X), evaluate :- (=> X (TransferResult V E)),
  old :- (List V), values :- (List V),
  succeeded :- (= (TransferResult (List V) E) (transferSource V E X xs evaluate)
                                           (TransferResult.ok (List V) E values))]
 (= (TransferExit V E) (transferTarget V E X xs evaluate old (fn [next :- (List V)] (TransferExit.done V E next)))
                      (TransferExit.done V E values))
 (exact (Eq.trans (transfer-refines V E X xs evaluate old (fn [next :- (List V)] (TransferExit.done V E next)))
          (congrArg (fn [answer :- (TransferResult (List V) E)]
                      (transferDispatch V E old answer (fn [next :- (List V)] (TransferExit.done V E next)))) succeeded))))
 (let [en (a/env)]
  (doseq [name theorem-names :let [d (env/lookup en (nm/from-string name))]]
   (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
    (throw (ex-info "Transfer theorem failed" {:theorem name})))) en)))

(def proof-state
  (delay
    (locking a/ansatz-env
      (let [previous @a/ansatz-env]
        (try (binding [*out* (java.io.StringWriter.)] (build!))
             (finally (reset! a/ansatz-env previous)))))))

(def model-identity
  (delay
    (let [description {:kernel @k/checker-version :imports (:cohort (k/proof-env))
                       :dependencies (k/closure @proof-state [(k/c "transfer-refines")
                                                             (k/c "transferSource")
                                                             (k/c "transferTarget")])}]
      {:id (core/sha256 (pr-str description)) :description description})))

(defn- app [name & args]
  (apply e/app* (if (#{"List.cons" "List.nil"} name) (k/c name [k/l0]) (k/c name)) args))
(defn- indices [arity]
  (reduce (fn [tail i] (app "List.cons" k/Nat (e/lit-nat (biginteger i)) tail))
          (app "List.nil" k/Nat) (reverse (range arity))))

(defn- goal-and-proof [arity]
  (let [[value error evaluate old] (repeatedly 4 k/fvar!)
        vv (e/fvar value) ve (e/fvar error) vf (e/fvar evaluate) vo (e/fvar old)
        result-type (app "TransferResult" vv ve) exit-type (app "TransferExit" vv ve)
        binders [[value "Value" k/Type0] [error "Error" k/Type0]
                 [evaluate "evaluate" (k/arrow k/Nat result-type)] [old "old" (k/List vv)]]
        program (indices arity) commit (app "TransferExit.done" vv ve)
        source (app "transferSource" vv ve k/Nat program vf)
        goal (k/pi* binders
               (k/eq exit-type (app "transferTarget" vv ve k/Nat program vf vo commit)
                     (app "transferDispatch" vv ve vo source commit)))
        proof (k/lam* binders (app "transfer-refines" vv ve k/Nat program vf vo commit))]
    {:goal goal :proof proof}))

(defn certify
  "Bind a compiler transfer plan to the universal ordering/commit theorem.
   Ordinals denote actual RHS positions; the adapter checks that table and all
   reads/commits. Evaluator/Long/named-scope/Java adequacy are separate bridges.
   This instantiates a checked theorem, without per-program tactic search."
  [destinations arguments plan]
  (let [shape (loop/check-transfer! destinations arguments plan)
        {:keys [goal proof]} (goal-and-proof (:arity shape))]
    (when-not (env/verifies? @proof-state goal proof)
      (throw (ex-info "Transfer instantiation rejected" {:reason :transfer-proof})))
    {:shape shape :goal goal :proof proof :checker-version :ordered-transfer-proof-v1
     :model-id (:id @model-identity)
     :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)
     :bridges [:source-and-plan-decoder :old-environment-evaluator :named-scope-and-slot-encoding
               :expression-lowering :Java-and-JVM :recovery-boundaries]}))

(defn verify? [destinations arguments plan receipt]
  (try
    (let [shape (loop/check-transfer! destinations arguments plan)
          {:keys [goal]} (goal-and-proof (:arity shape))]
      (and (= :ordered-transfer-proof-v1 (:checker-version receipt))
           (= (:id @model-identity) (:model-id receipt))
           (= shape (:shape receipt)) (= goal (:goal receipt))
           (= (k/expr-hash goal) (:goal-sha256 receipt))
           (= (k/expr-hash (:proof receipt)) (:proof-sha256 receipt))
           (env/verifies? @proof-state goal (:proof receipt))))
    (catch Exception _ false)))
