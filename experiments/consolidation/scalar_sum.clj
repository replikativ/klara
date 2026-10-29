(ns consolidation.scalar-sum
  "A concrete reachable-accumulator invariant for the sum consumer. The input
   vector/functional-environment and T0/JVM bridges remain explicit."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm] [consolidation.scalar-driver :as driver]))
(def theorem-names ["scalar-budget-acc" "scalar-budget-value" "scalar-budget-sum" "scalar-budget-start"
                    "scalar-sum-budget-step" "scalar-sum-run-safe" "scalar-sum-prefix-total"])
(defn prove! []
  (binding [*ns* (the-ns 'consolidation.scalar-sum)]
    (reset! a/ansatz-env @driver/proof-state)
    (a/defn scalarSumCore [] ScalarCore (ScalarCore.add (ScalarCore.local 1) (ScalarCore.local 0)))
    (a/theorem scalar-sum-budget-step
      [acc :- Nat, value :- Nat, remaining :- Nat, upper :- Nat, hv :- (<= value upper)]
      (<= (+ (+ acc value) (* remaining upper)) (+ acc (* (Nat.succ remaining) upper)))
      (rw Nat.succ_mul) (omega))
    (a/theorem scalar-budget-acc
      [a :- Nat, v :- Nat, n :- Nat, u :- Nat, cap :- Nat, h :- (<= (+ (+ a v) (* n u)) cap)]
      (<= a cap) (omega))
    (a/theorem scalar-budget-value
      [a :- Nat, v :- Nat, n :- Nat, u :- Nat, cap :- Nat, h :- (<= (+ (+ a v) (* n u)) cap)]
      (<= v cap) (omega))
    (a/theorem scalar-budget-sum
      [a :- Nat, v :- Nat, n :- Nat, u :- Nat, cap :- Nat, h :- (<= (+ (+ a v) (* n u)) cap)]
      (<= (+ a v) cap) (omega))
    (a/theorem scalar-sum-run-safe
      [xs :- (List Nat), upper :- Nat, cap :- Nat,
       elements :- (forall [i :- Nat] (<= (scalarAt xs i) upper))]
      (forall [count :- Nat, index :- Nat, acc :- Nat,
               budget :- (<= (+ acc (* count upper)) cap)]
        (ScalarRunSafe cap scalarSumCore xs count index acc))
      (intro count) (induction count)
      (all_goals (intro index) (intro acc) (intro budget))
      (all_goals (try (exact (ScalarRunSafe.done cap scalarSumCore xs index acc))))
      (exact ((fn [nextBudget :- (Nat.le (+ (+ acc (scalarAt xs index)) (* n upper)) cap)]
                (ScalarRunSafe.step cap scalarSumCore xs n index acc (+ acc (scalarAt xs index))
                  (ScalarBound.add cap (scalarPush (scalarAt xs index) (scalarPush acc scalarZero))
                    (ScalarCore.local 1) (ScalarCore.local 0) acc (scalarAt xs index)
                    (ScalarBound.local cap (scalarPush (scalarAt xs index) (scalarPush acc scalarZero)) 1 (scalar-budget-acc acc (scalarAt xs index) n upper cap nextBudget))
                    (ScalarBound.local cap (scalarPush (scalarAt xs index) (scalarPush acc scalarZero)) 0 (scalar-budget-value acc (scalarAt xs index) n upper cap nextBudget))
                    (scalar-budget-sum acc (scalarAt xs index) n upper cap nextBudget))
                  (ih_n (Nat.succ index) (+ acc (scalarAt xs index)) nextBudget)))
              (Nat.le_trans (scalar-sum-budget-step acc (scalarAt xs index) n upper (elements index)) budget))))
    (a/theorem scalar-budget-start [n :- Nat, u :- Nat, cap :- Nat, budget :- (<= (* n u) cap)]
      (<= (+ 0 (* n u)) cap)
      (rw Nat.zero_add) (all_goals (exact budget)))
    (a/theorem scalar-sum-prefix-total
      [xs :- (List Nat), upper :- Nat, cap :- Nat, count :- Nat,
       elements :- (forall [i :- Nat] (<= (scalarAt xs i) upper)),
       within :- (<= count (List.length xs)), budget :- (<= (* count upper) cap)]
      (= (Option Nat) (scalarRunChecked count scalarSumCore xs 0 0 cap)
         (Option.some Nat (List.foldl (scalarStep scalarSumCore) 0 (scalarTake xs count))))
      (exact (scalar-checked-prefix-fold xs scalarSumCore count 0 cap within
               (scalar-sum-run-safe xs upper cap elements count 0 0 (scalar-budget-start count upper cap budget)))))
    (let [en (a/env)]
      (doseq [name theorem-names :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "sum invariant theorem failed" {:theorem name})))) en)))
(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))
