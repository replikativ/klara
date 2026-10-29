(ns consolidation.demand-model
  "Total finite-list demand laws and a separate bounded observation model.
   Fuel exhaustion is pending, not a source error or a divergence proof."
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as nm]
            [consolidation.producer-model :as producer] [klara.fusion.kernel :as k]))

(defn prove! []
  (binding [*ns* (the-ns 'consolidation.demand-model)]
    (reset! a/ansatz-env @producer/proof-state)
    (a/defn demandTake [xs :- (List Nat)] (=> Nat (List Nat))
      (match xs
        [nil (fn [n :- Nat] (List.nil Nat))]
        [(cons x rest) (fn [n :- Nat]
                         (match n [zero (List.nil Nat)]
                                  [(succ previous) (List.cons Nat x (demandTake rest previous))]))]))
    (a/theorem demand-take-map
      [f :- (=> Nat Nat), xs :- (List Nat)]
      (forall [n :- Nat]
        (= (List Nat) (demandTake (List.map f xs) n)
           (List.map f (demandTake xs n))))
      (induction xs)
      (all_goals (intro n))
      (all_goals (try (rfl)))
      (all_goals (cases n))
      (all_goals (try (rfl)))
      (exact (congrArg (fn [values :- (List Nat)] (List.cons Nat (f head) values)) (ih_tail n))))
    (a/inductive DemandPlan [] (done) (yield [value Nat] [rest DemandPlan]) (fault [category Nat]) (spin))
    (a/inductive DemandObservation []
      (ok [values (List Nat)]) (fault [values (List Nat)] [category Nat]) (pending [values (List Nat)]))
    (a/defn demandCons [x :- Nat, observation :- DemandObservation] DemandObservation
      (match observation
        [(ok values) (DemandObservation.ok (List.cons Nat x values))]
        [(fault values category) (DemandObservation.fault (List.cons Nat x values) category)]
        [(pending values) (DemandObservation.pending (List.cons Nat x values))]))
    (a/defn demandZeroFuel [n :- Nat] DemandObservation
      (match n [zero (DemandObservation.ok (List.nil Nat))]
               [(succ previous) (DemandObservation.pending (List.nil Nat))]))
    (a/defn demandObserve [fuel :- Nat] (=> Nat (=> DemandPlan DemandObservation))
      (match fuel
        [zero (fn [n :- Nat, p :- DemandPlan] (demandZeroFuel n))]
        [(succ remaining)
         (fn [n :- Nat, p :- DemandPlan]
           (match n
             [zero (DemandObservation.ok (List.nil Nat))]
             [(succ previous)
              (match p
                [done (DemandObservation.ok (List.nil Nat))]
                [(yield value rest) (demandCons value (demandObserve remaining previous rest))]
                [(fault category) (DemandObservation.fault (List.nil Nat) category)]
                [spin (demandObserve remaining (Nat.succ previous) DemandPlan.spin)])]))]))
    (a/theorem demand-zero-elements
      [fuel :- Nat, p :- DemandPlan]
      (= DemandObservation (demandObserve fuel 0 p) (DemandObservation.ok (List.nil Nat)))
      (cases fuel) (all_goals (rfl)))
    (a/theorem demand-prefix-ignores-tail
      [fuel :- Nat, x :- Nat, rest :- DemandPlan]
      (= DemandObservation (demandObserve (Nat.succ fuel) 1 (DemandPlan.yield x rest))
         (DemandObservation.ok (List.cons Nat x (List.nil Nat))))
      (cases fuel) (all_goals (rfl)))
    (a/theorem demand-spin-pending
      [fuel :- Nat, n :- Nat]
      (= DemandObservation (demandObserve fuel (Nat.succ n) DemandPlan.spin)
         (DemandObservation.pending (List.nil Nat)))
      (induction fuel)
      (all_goals (try (rfl)))
      (exact ih_n))
    (let [en (a/env)]
      (doseq [name ["demand-take-map" "demand-zero-elements" "demand-prefix-ignores-tail" "demand-spin-pending"]
              :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "demand theorem check failed" {:theorem name})))) en)))
(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))

(defn prefix-witness [bound-proof prefix]
  (let [term (:term bound-proof) x (k/fvar!) xs (k/fvar!)
        f (k/lam* [[x "x" k/Nat]] (e/app* (k/c "boundValue") term (e/fvar x)))
        n (e/lit-nat (biginteger prefix))
        take* (fn [values] (e/app* (k/c "demandTake") values n))
        goal (k/pi* [[xs "xs" (k/List k/Nat)]]
                     (k/eq (k/List k/Nat)
                           (take* (k/lmap k/Nat k/Nat f (e/fvar xs)))
                           (k/lmap k/Nat k/Nat f (take* (e/fvar xs)))))
        proof (k/lam* [[xs "xs" (k/List k/Nat)]]
                      (e/app* (k/c "demand-take-map") f (e/fvar xs) n))]
    (when-not (env/verifies? @proof-state goal proof)
      (throw (ex-info "prefix witness rejected" {:reason :demand-proof})))
    {:goal goal :proof proof :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)}))

(defn sum-witness [bound-proof prefix]
  (let [term (:term bound-proof) [x xs values] (repeatedly 3 k/fvar!)
        f (k/lam* [[x "x" k/Nat]] (e/app* (k/c "boundValue") term (e/fvar x)))
        n (e/lit-nat (biginteger prefix))
        take* #(e/app* (k/c "demandTake") % n)
        left (take* (k/lmap k/Nat k/Nat f (e/fvar xs)))
        right (k/lmap k/Nat k/Nat f (take* (e/fvar xs)))
        sum* #(k/foldl k/Nat k/Nat (k/c "Nat.add") (e/lit-nat 0) %)
        goal (k/pi* [[xs "xs" (k/List k/Nat)]] (k/eq k/Nat (sum* left) (sum* right)))
        equality (e/app* (k/c "demand-take-map") f (e/fvar xs) n)
        proof (k/lam* [[xs "xs" (k/List k/Nat)]]
                      (e/app* (k/c "congrArg" [k/l1 k/l1]) (k/List k/Nat) k/Nat left right
                              (k/lam* [[values "values" (k/List k/Nat)]] (sum* (e/fvar values))) equality))]
    (when-not (env/verifies? @proof-state goal proof)
      (throw (ex-info "prefix sum witness rejected" {:reason :demand-proof})))
    {:goal goal :proof proof :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)}))
