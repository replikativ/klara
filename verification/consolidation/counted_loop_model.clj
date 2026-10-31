(ns consolidation.counted-loop-model
  "Checked composition of simultaneous scalar updates and bounded backedges."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [consolidation.scalar-block :as block]))

(def theorem-names ["loop-step-refines" "loop-bind-congr" "loop-bind-assoc" "loop-runs-refine" "loop-runs-split"
                    "loop-commit-index" "loop-commit-acc" "loop-count-enter"
                    "loop-count-backedge" "loop-count-exit" "loop-counter-fits" "loop-chunk-end-fits"])

(defn prove! []
  (binding [*ns* (the-ns 'consolidation.counted-loop-model)]
    (reset! a/ansatz-env @block/proof-state)
    (clojure.core/refer 'consolidation.scalar-core :only '[scalarPush scalarChecked])
    (clojure.core/refer 'consolidation.scalar-block :only '[slotRun slotStore])
    (a/inductive LoopState [] (state [index Nat] [acc Nat]))
    (a/defn loopEnv [state :- LoopState] (=> Nat Nat)
      (match state [(state index acc) (scalarPush acc (scalarPush index (fn [i :- Nat] 0)))]))
    (a/defn loopPair [left :- (Option Nat), right :- (=> Nat (Option Nat))] (Option LoopState)
      (match left
        [none (Option.none LoopState)]
        [(some i) (match (right i) [none (Option.none LoopState)]
                                  [(some acc) (Option.some LoopState (LoopState.state i acc))])]))
    (a/defn loopSourceStep [index :- ScalarCore, acc :- ScalarCore, cap :- Nat, state :- LoopState] (Option LoopState)
      (loopPair (scalarChecked index (loopEnv state) cap)
                (fn [ignored :- Nat] (scalarChecked acc (loopEnv state) cap))))
    (a/defn loopTargetStep [index :- SlotBlock, acc :- SlotBlock, cap :- Nat, state :- LoopState] (Option LoopState)
      (loopPair (slotRun index (loopEnv state) cap)
                (fn [ignored :- Nat] (slotRun acc (loopEnv state) cap))))
    (a/defn loopBind [answer :- (Option LoopState), f :- (=> LoopState (Option LoopState))] (Option LoopState)
      (match answer [none (Option.none LoopState)] [(some state) (f state)]))
    (a/defn loopRun [count :- Nat] (=> (=> LoopState (Option LoopState)) (=> LoopState (Option LoopState)))
      (match count
        [zero (fn [step :- (=> LoopState (Option LoopState)), state :- LoopState] (Option.some LoopState state))]
        [(succ remaining) (fn [step :- (=> LoopState (Option LoopState)), state :- LoopState]
                            (loopBind (step state) (fn [next :- LoopState] (loopRun remaining step next))))]))
    (a/theorem loop-step-refines
      [index :- ScalarCore, acc :- ScalarCore, bi :- SlotBlock, ba :- SlotBlock,
       hi :- (forall [rho :- (=> Nat Nat), cap :- Nat] (= (Option Nat) (slotRun bi rho cap) (scalarChecked index rho cap))),
       ha :- (forall [rho :- (=> Nat Nat), cap :- Nat] (= (Option Nat) (slotRun ba rho cap) (scalarChecked acc rho cap)))]
      (forall [cap :- Nat, state :- LoopState]
        (= (Option LoopState) (loopTargetStep bi ba cap state) (loopSourceStep index acc cap state)))
      (intro cap) (intro state)
      (simp only [loopTargetStep loopSourceStep])
      (rw [(hi (loopEnv state) cap) (ha (loopEnv state) cap)]))
    (a/theorem loop-bind-congr
      [answer :- (Option LoopState), f :- (=> LoopState (Option LoopState)), g :- (=> LoopState (Option LoopState)),
       h :- (forall [s :- LoopState] (= (Option LoopState) (f s) (g s)))]
      (= (Option LoopState) (loopBind answer f) (loopBind answer g))
      (cases answer) (all_goals (simp only [loopBind]))
      (all_goals (try (rfl))) (exact (h val)))
    (a/theorem loop-bind-assoc
      [answer :- (Option LoopState), f :- (=> LoopState (Option LoopState)), g :- (=> LoopState (Option LoopState))]
      (= (Option LoopState) (loopBind (loopBind answer f) g)
                           (loopBind answer (fn [state :- LoopState] (loopBind (f state) g))))
      (cases answer) (all_goals (rfl)))
    (a/theorem loop-runs-refine
      [source :- (=> LoopState (Option LoopState)), target :- (=> LoopState (Option LoopState)),
       step :- (forall [s :- LoopState] (= (Option LoopState) (target s) (source s))), count :- Nat]
      (forall [state :- LoopState]
        (= (Option LoopState) (loopRun count target state) (loopRun count source state)))
      (induction count) (all_goals (intro state))
      (all_goals (simp only [loopRun.eq_1 loopRun.eq_2]))
      (all_goals (try (rfl)))
      (rw [(step state)])
      (exact (loop-bind-congr (source state)
               (fn [next :- LoopState] (loopRun n target next))
               (fn [next :- LoopState] (loopRun n source next)) ih_n)))
    (a/theorem loop-runs-split [first :- Nat]
      (forall [second :- Nat, step :- (=> LoopState (Option LoopState)), state :- LoopState]
        (= (Option LoopState) (loopRun (+ first second) step state)
           (loopBind (loopRun first step state) (fn [next :- LoopState] (loopRun second step next)))))
      (induction first)
      (all_goals (intro second) (intro step) (intro state))
      (all_goals (try (exact (congrArg (fn [count :- Nat] (loopRun count step state)) (Nat.zero_add second)))))
      (exact (Eq.trans
               (congrArg (fn [count :- Nat] (loopRun count step state)) (Nat.succ_add n second))
               (Eq.trans
               (loop-bind-congr (step state)
                 (fn [next :- LoopState] (loopRun (+ n second) step next))
                 (fn [next :- LoopState] (loopBind (loopRun n step next)
                                           (fn [last :- LoopState] (loopRun second step last))))
                 (fn [next :- LoopState] (ih_n second step next)))
               (Eq.symm (loop-bind-assoc (step state)
                          (fn [next :- LoopState] (loopRun n step next))
                          (fn [next :- LoopState] (loopRun second step next))))))))
    ;; Both RHSs are computed from old loopEnv before these writes. These
    ;; equations justify committing their values; they do not justify motion
    ;; of an RHS after the first write.
    (a/theorem loop-commit-index [rho :- (=> Nat Nat), nextIndex :- Nat, nextAcc :- Nat]
      (= Nat (slotStore (slotStore rho 1 nextIndex) 0 nextAcc 1) nextIndex) (rfl))
    (a/theorem loop-commit-acc [rho :- (=> Nat Nat), nextIndex :- Nat, nextAcc :- Nat]
      (= Nat (slotStore (slotStore rho 1 nextIndex) 0 nextAcc 0) nextAcc) (rfl))
    (a/theorem loop-count-backedge [index :- Nat, remaining :- Nat, limit :- Nat,
                                   h :- (= Nat (+ index (Nat.succ remaining)) limit)]
      (= Nat (+ (Nat.succ index) remaining) limit) (omega))
    (a/theorem loop-count-enter [index :- Nat, remaining :- Nat, limit :- Nat,
                                h :- (= Nat (+ index (Nat.succ remaining)) limit)]
      (= Bool (Nat.ble (Nat.succ index) limit) true)
      (apply Nat.ble_eq_true_of_le) (omega))
    (a/theorem loop-count-exit [index :- Nat, limit :- Nat, h :- (= Nat (+ index 0) limit)]
      (= Nat index limit) (omega))
    (a/theorem loop-counter-fits [index :- Nat, limit :- Nat, cap :- Nat,
                                 within :- (<= (Nat.succ index) limit), bound :- (<= limit cap)]
      (<= (Nat.succ index) cap) (omega))
    (a/theorem loop-chunk-end-fits [index :- Nat, limit :- Nat, count :- Nat,
                                  within :- (<= index limit), quota :- (<= count (- limit index))]
      (<= (+ index count) limit) (omega))
    (let [en (a/env)]
      (doseq [name theorem-names :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "Counted loop theorem rejected" {:theorem name}))))
      en)))

(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))
