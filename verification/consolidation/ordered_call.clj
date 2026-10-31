(ns consolidation.ordered-call
  "Stateful ordered-argument/let model. Binding freshening and Core/CEK/JVM
   correspondence are explicit implementation bridges, not consequences of
   this model's termination or equality theorem."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm] [klara.fusion.kernel :as k]))

(def theorem-names ["call-dispatch-prepend" "call-head-refines" "ordered-call-refines"
                    "recipe-observations-compose"])

(defn- build! []
  (binding [*ns* (the-ns 'consolidation.ordered-call)]
    (reset! a/ansatz-env (k/env*))
    (a/inductive CallAnswer [V Type S Type E Type]
      (done [resultValue V] [resultState S])
      (failed [error E] [errorState S]))
    (a/defn callPrepend [V :- Type, S :- Type, E :- Type, value :- V,
                        answer :- (CallAnswer (List V) S E)] (CallAnswer (List V) S E)
      (match answer
        [(done values state) (CallAnswer.done (List V) S E (List.cons V value values) state)]
        [(failed error state) (CallAnswer.failed (List V) S E error state)]))
    (a/defn callArguments [V :- Type, S :- Type, E :- Type, X :- Type, xs :- (List X)]
      (=> (=> X (=> S (CallAnswer V S E))) (=> S (CallAnswer (List V) S E)))
      (match xs
        [nil (fn [evaluate :- (=> X (=> S (CallAnswer V S E))), state :- S]
               (CallAnswer.done (List V) S E (List.nil V) state))]
        [(cons head tail)
         (fn [evaluate :- (=> X (=> S (CallAnswer V S E))), state :- S]
           (match (evaluate head state)
             [(failed error next) (CallAnswer.failed (List V) S E error next)]
             [(done value next) (callPrepend V S E value (callArguments V S E X tail evaluate next))]))]))
    (a/defn callDispatch [V :- Type, S :- Type, E :- Type,
                         answer :- (CallAnswer (List V) S E),
                         body :- (=> (List V) (=> S (CallAnswer V S E)))] (CallAnswer V S E)
      (match answer [(failed error state) (CallAnswer.failed V S E error state)]
                    [(done values state) (body values state)]))
    (a/defn orderedLets [V :- Type, S :- Type, E :- Type, X :- Type, xs :- (List X)]
      (=> (=> X (=> S (CallAnswer V S E))) (=> S (=> (=> (List V) (=> S (CallAnswer V S E)))
                                                  (CallAnswer V S E))))
      (match xs
        [nil (fn [evaluate :- (=> X (=> S (CallAnswer V S E))), state :- S,
                  body :- (=> (List V) (=> S (CallAnswer V S E)))]
               (body (List.nil V) state))]
        [(cons head tail)
         (fn [evaluate :- (=> X (=> S (CallAnswer V S E))), state :- S,
              body :- (=> (List V) (=> S (CallAnswer V S E)))]
           (match (evaluate head state)
             [(failed error next) (CallAnswer.failed V S E error next)]
             [(done value next)
              (orderedLets V S E X tail evaluate next
                (fn [values :- (List V), final :- S] (body (List.cons V value values) final)))]))]))
    (a/theorem call-dispatch-prepend
      [V :- Type, S :- Type, E :- Type, value :- V, answer :- (CallAnswer (List V) S E),
       body :- (=> (List V) (=> S (CallAnswer V S E)))]
      (= (CallAnswer V S E)
         (callDispatch V S E (callPrepend V S E value answer) body)
         (callDispatch V S E answer
           (fn [values :- (List V), state :- S] (body (List.cons V value values) state))))
      (cases answer) (all_goals (rfl)))
    (a/defn callSourceHead [V :- Type, S :- Type, E :- Type, answer :- (CallAnswer V S E),
                           tail :- (=> S (CallAnswer (List V) S E))] (CallAnswer (List V) S E)
      (match answer
        [(failed error state) (CallAnswer.failed (List V) S E error state)]
        [(done value state) (callPrepend V S E value (tail state))]))
    (a/defn callTargetHead [V :- Type, S :- Type, E :- Type, answer :- (CallAnswer V S E),
                           tail :- (=> S (=> (=> (List V) (=> S (CallAnswer V S E))) (CallAnswer V S E))),
                           body :- (=> (List V) (=> S (CallAnswer V S E)))] (CallAnswer V S E)
      (match answer
        [(failed error state) (CallAnswer.failed V S E error state)]
        [(done value state) (tail state
                             (fn [values :- (List V), final :- S]
                               (body (List.cons V value values) final)))]))
    (a/theorem call-head-refines
      [V :- Type, S :- Type, E :- Type, answer :- (CallAnswer V S E),
       sourceTail :- (=> S (CallAnswer (List V) S E)),
       targetTail :- (=> S (=> (=> (List V) (=> S (CallAnswer V S E))) (CallAnswer V S E))),
       agreement :- (forall [state :- S, body :- (=> (List V) (=> S (CallAnswer V S E)))]
                     (= (CallAnswer V S E) (targetTail state body)
                        (callDispatch V S E (sourceTail state) body))),
       body :- (=> (List V) (=> S (CallAnswer V S E)))]
      (= (CallAnswer V S E) (callTargetHead V S E answer targetTail body)
         (callDispatch V S E (callSourceHead V S E answer sourceTail) body))
      (cases answer) (all_goals (try (rfl)))
      (exact (Eq.trans
               (agreement resultState
                 (fn [values :- (List V), state :- S] (body (List.cons V resultValue values) state)))
               (Eq.symm (call-dispatch-prepend V S E resultValue (sourceTail resultState) body)))))
    (a/theorem ordered-call-refines
      [V :- Type, S :- Type, E :- Type, X :- Type, xs :- (List X)]
      (forall [evaluate :- (=> X (=> S (CallAnswer V S E))), state :- S,
               body :- (=> (List V) (=> S (CallAnswer V S E)))]
        (= (CallAnswer V S E) (orderedLets V S E X xs evaluate state body)
           (callDispatch V S E (callArguments V S E X xs evaluate state) body)))
      (induction xs)
      (all_goals (intro evaluate) (intro state) (intro body))
      (all_goals (try (rfl)))
      (exact (call-head-refines V S E (evaluate head state)
               (fn [next :- S] (callArguments V S E X tail evaluate next))
               (fn [next :- S, nextBody :- (=> (List V) (=> S (CallAnswer V S E)))]
                 (orderedLets V S E X tail evaluate next nextBody))
               (ih_tail evaluate) body)))
    (a/theorem recipe-observations-compose
      [A :- Type, B :- Type, C :- Type, O :- Type,
       first :- (=> A B), second :- (=> B C), sourceObs :- (=> A O),
       middleObs :- (=> B O), targetObs :- (=> C O),
       firstCorrect :- (forall [x :- A] (= O (middleObs (first x)) (sourceObs x))),
       secondCorrect :- (forall [x :- B] (= O (targetObs (second x)) (middleObs x))), x :- A]
      (= O (targetObs (second (first x))) (sourceObs x))
      (exact (Eq.trans (secondCorrect (first x)) (firstCorrect x))))
  @a/ansatz-env))

(defonce proof-state
  (delay
    (locking a/ansatz-env
      (let [previous @a/ansatz-env]
        (try (binding [*out* (java.io.StringWriter.)] (build!))
             (finally (reset! a/ansatz-env previous)))))))

(defn verify-theorems! []
  (mapv (fn [name]
          (let [en @proof-state d (env/lookup en (nm/from-string name))
                proof (env/ci-value d) goal (env/ci-type d)
                accepted (env/verifies? en goal proof)
                self-reference (contains? (k/constants-of proof) name)]
            (when-not (and accepted (not self-reference))
              (throw (ex-info "ordered-call theorem rejected" {:theorem name})))
            {:theorem name :kernel-accepted accepted :self-reference self-reference
             :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)})) theorem-names))
