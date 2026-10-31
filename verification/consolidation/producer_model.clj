(ns consolidation.producer-model
  (:require [ansatz.core :as a] [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e] [ansatz.kernel.name :as nm]
            [consolidation.interval :as interval] [klara.fusion.kernel :as k]))

(defn prove! []
  (binding [*ns* (the-ns 'consolidation.producer-model)]
    (reset! a/ansatz-env @interval/proof-state)
    (a/inductive AllBelow [] :in Prop :indices [bound Nat, xs (List Nat)]
      (nil [bound Nat] :where [bound (List.nil Nat)])
      (cons [bound Nat] [x Nat] [rest (List Nat)] [hx (Nat.le x bound)] [hr (AllBelow bound rest)]
            :where [bound (List.cons Nat x rest)]))
    (a/theorem producer-bound-weaken
      [lower :- Nat, xs :- (List Nat), hs :- (AllBelow lower xs)]
      (forall [upper :- Nat, h :- (<= lower upper)] (AllBelow upper xs))
      (induction hs)
      (all_goals (intro upper) (intro h))
      (all_goals (try (exact (AllBelow.nil upper))))
      (all_goals (exact (AllBelow.cons upper x rest (Nat.le_trans hx h) (ih_hr upper h)))))
    (a/theorem producer-map-bound
      [p :- BoundExpr, bound :- Nat, xs :- (List Nat), hs :- (AllBelow bound xs)]
      (AllBelow (boundValue p bound) (List.map (fn [x :- Nat] (boundValue p x)) xs))
      (induction hs)
      (all_goals (try (exact (AllBelow.nil (boundValue p bound)))))
      (all_goals (exact (AllBelow.cons (boundValue p bound) (boundValue p x)
                                     (List.map (fn [v :- Nat] (boundValue p v)) rest)
                                     (bound-monotone p x bound hx) ih_hr))))
    (let [en (a/env)]
      (doseq [name ["producer-bound-weaken" "producer-map-bound"]
              :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "producer model proof failed" {:theorem name})))) en)))
(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))

(defn witness [bound-proof max-x]
  (let [term (:term bound-proof) bound (e/lit-nat (biginteger max-x))
        upper (e/lit-nat (biginteger (:upper bound-proof))) xs (k/fvar!) hs (k/fvar!)
        below (fn [b vs] (e/app* (k/c "AllBelow") b vs))
        x (k/fvar!) f (k/lam* [[x "x" k/Nat]] (e/app* (k/c "boundValue") term (e/fvar x)))
        goal (k/pi* [[xs "xs" (k/List k/Nat)] [hs "bounded" (below bound (e/fvar xs))]]
                     (below upper (k/lmap k/Nat k/Nat f (e/fvar xs))))
        proof (k/lam* [[xs "xs" (k/List k/Nat)] [hs "bounded" (below bound (e/fvar xs))]]
                      (e/app* (k/c "producer-map-bound") term bound (e/fvar xs) (e/fvar hs)))]
    (when-not (env/verifies? @proof-state goal proof)
      (throw (ex-info "producer bound witness rejected" {:reason :producer-proof})))
    {:goal goal :proof proof :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)}))
