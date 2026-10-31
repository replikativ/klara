(ns consolidation.enclosed-consumer
  "Lift the finite private-state simulation through an enclosed pure consumer.
   The consumer observes the final value, not retained versions or identity.
   Core extraction, checked-Long semantics and JVM erasure remain bridges."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [consolidation.private-state :as private] [klara.fusion.kernel :as k]))

(def theorem-names ["private-enclosed-consumer-refines" "private-enclosed-releases"
                    "private-enclosed-checked-consumer-refines" "private-source-failure-precedes-consumer"])

(defn- build! []
  (binding [*ns* (the-ns 'consolidation.enclosed-consumer)]
    (reset! a/ansatz-env (:environment @private/proof-state))
    (a/inductive EnclosedAnswer []
      (value [result Bool] [outside (List Nat)])
      (error [category Nat] [outside (List Nat)]))
    (a/defn enclosedObserve [answer :- PrivateAnswer, consume :- (=> Nat Bool)] EnclosedAnswer
      (match answer
        [(ok value history outside) (EnclosedAnswer.value (consume value) outside)]
        [(error category outside) (EnclosedAnswer.error category outside)]))
    (a/defn enclosedExitObserve [exit :- PrivateExit, consume :- (=> Nat Bool)] EnclosedAnswer
      (match exit [(mk answer released) (enclosedObserve answer consume)]))
    (a/defn enclosedReleased [exit :- PrivateExit] Bool
      (match exit [(mk answer released) released]))
    (a/inductive ConsumerAnswer [] (value [result Bool]) (error [category Nat]))
    (a/defn enclosedConsume [answer :- ConsumerAnswer, outside :- (List Nat)] EnclosedAnswer
      (match answer
        [(value result) (EnclosedAnswer.value result outside)]
        [(error category) (EnclosedAnswer.error category outside)]))
    (a/defn enclosedCheckedObserve [answer :- PrivateAnswer, consume :- (=> Nat ConsumerAnswer)] EnclosedAnswer
      (match answer
        [(ok value history outside) (enclosedConsume (consume value) outside)]
        [(error category outside) (EnclosedAnswer.error category outside)]))
    (a/defn enclosedCheckedExitObserve [exit :- PrivateExit, consume :- (=> Nat ConsumerAnswer)] EnclosedAnswer
      (match exit [(mk answer released) (enclosedCheckedObserve answer consume)]))
    (a/theorem private-enclosed-consumer-refines
      [p :- PrivatePlan, safe :- (PrivateSafe p), x :- Nat, history :- (List Nat),
       outside :- (List Nat), cap :- Nat, consume :- (=> Nat Bool)]
      (= EnclosedAnswer
         (enclosedExitObserve (privateTarget p (PrivateCell.mk x) history 0 outside cap) consume)
         (enclosedObserve (privateSource p x history outside cap) consume))
      (rw [(private-state-simulation p safe x history outside cap)])
      (all_goals (rfl)))
    (a/theorem private-enclosed-releases
      [p :- PrivatePlan, safe :- (PrivateSafe p), x :- Nat, history :- (List Nat),
       outside :- (List Nat), cap :- Nat]
      (= Bool (enclosedReleased (privateTarget p (PrivateCell.mk x) history 0 outside cap)) true)
      (rw [(private-state-simulation p safe x history outside cap)])
      (all_goals (rfl)))
    (a/theorem private-enclosed-checked-consumer-refines
      [p :- PrivatePlan, safe :- (PrivateSafe p), x :- Nat, history :- (List Nat),
       outside :- (List Nat), cap :- Nat, consume :- (=> Nat ConsumerAnswer)]
      (= EnclosedAnswer
         (enclosedCheckedExitObserve (privateTarget p (PrivateCell.mk x) history 0 outside cap) consume)
         (enclosedCheckedObserve (privateSource p x history outside cap) consume))
      (rw [(private-state-simulation p safe x history outside cap)])
      (all_goals (rfl)))
    (a/theorem private-source-failure-precedes-consumer
      [category :- Nat, outside :- (List Nat), consume :- (=> Nat ConsumerAnswer)]
      (= EnclosedAnswer (enclosedCheckedObserve (PrivateAnswer.error category outside) consume)
         (EnclosedAnswer.error category outside))
      (rfl)))
  @a/ansatz-env)

(def proof-state
  (delay (locking a/ansatz-env
           (let [previous @a/ansatz-env]
             (try (binding [*out* (java.io.StringWriter.)] (build!))
                  (finally (reset! a/ansatz-env previous)))))))

(defn verify-theorems! []
  (mapv (fn [name]
          (let [en @proof-state d (env/lookup en (nm/from-string name))
                goal (env/ci-type d) proof (env/ci-value d)
                accepted (env/verifies? en goal proof)
                self-reference (contains? (k/constants-of proof) name)]
            (when-not (and accepted (not self-reference))
              (throw (ex-info "enclosed consumer theorem rejected" {:theorem name})))
            {:theorem name :kernel-accepted accepted :self-reference self-reference
             :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)})) theorem-names))
