(ns consolidation.private-state
  "Kernel model for the first private-accumulator simulation. This file models
   finite instruction plans, not all core terms or JVM arrays. Its extraction
   and T0 correspondence remain tested/trusted bridges."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [klara.fusion.kernel :as k]))

(defn prove! []
  (binding [*ns* (the-ns 'consolidation.private-state)]
  (a/load-init!)
  (a/inductive PrivatePlan []
    (done)
    (bump [tail PrivatePlan])
    (check [ok Bool] [tail PrivatePlan])
    (alias [tail PrivatePlan])
    (retain [tail PrivatePlan])
    (branch [condition Bool] [left PrivatePlan] [right PrivatePlan]))
  (a/inductive PrivateAnswer []
    (ok [value Nat] [history (List Nat)] [outside (List Nat)])
    (error [category Nat] [outside (List Nat)]))
  (a/inductive PrivateCell [] (mk [value Nat]))
  (a/inductive PrivateExit [] (mk [answer PrivateAnswer] [released Bool]))
  (a/inductive PrivateSafe [] :in Prop :indices [p PrivatePlan]
    (done :where [PrivatePlan.done])
    (bump [tail PrivatePlan] [h (PrivateSafe tail)] :where [(PrivatePlan.bump tail)])
    (check [ok Bool] [tail PrivatePlan] [h (PrivateSafe tail)] :where [(PrivatePlan.check ok tail)])
    (alias [tail PrivatePlan] [h (PrivateSafe tail)] :where [(PrivatePlan.alias tail)])
    (branch [condition Bool] [left PrivatePlan] [right PrivatePlan]
            [hl (PrivateSafe left)] [hr (PrivateSafe right)]
            :where [(PrivatePlan.branch condition left right)]))
  (a/defn privateRead [cell :- PrivateCell] Nat (match cell [(mk value) value]))
  (a/defn privateCopies [n :- Nat] (=> Nat (=> (List Nat) (List Nat)))
    (match n
      [zero (fn [value :- Nat, rest :- (List Nat)] rest)]
      [(succ previous) (fn [value :- Nat, rest :- (List Nat)]
                         (List.cons Nat value (privateCopies previous value rest)))]))
  (a/defn privateSource [p :- PrivatePlan]
    (=> Nat (=> (List Nat) (=> (List Nat) (=> Nat PrivateAnswer))))
    (match p
      [done (fn [x :- Nat, history :- (List Nat), outside :- (List Nat), cap :- Nat]
              (PrivateAnswer.ok x history outside))]
      [(bump tail) (fn [x :- Nat, history :- (List Nat), outside :- (List Nat), cap :- Nat]
                     (match (Nat.blt x cap)
                       [true (privateSource tail (+ x 1) history outside cap)]
                       [false (PrivateAnswer.error 0 outside)]))]
      [(check ok tail) (fn [x :- Nat, history :- (List Nat), outside :- (List Nat), cap :- Nat]
                         (match ok
                           [true (privateSource tail x history outside cap)]
                           [false (PrivateAnswer.error 1 outside)]))]
      [(alias tail) (fn [x :- Nat, history :- (List Nat), outside :- (List Nat), cap :- Nat]
                      (privateSource tail x history outside cap))]
      [(retain tail) (fn [x :- Nat, history :- (List Nat), outside :- (List Nat), cap :- Nat]
                       (privateSource tail x (List.cons Nat x history) outside cap))]
      [(branch condition left right)
       (fn [x :- Nat, history :- (List Nat), outside :- (List Nat), cap :- Nat]
         (match condition
           [true (privateSource left x history outside cap)]
           [false (privateSource right x history outside cap)]))]))
  (a/defn privateTarget [p :- PrivatePlan]
    (=> PrivateCell (=> (List Nat) (=> Nat (=> (List Nat) (=> Nat PrivateExit)))))
    (match p
      [done (fn [cell :- PrivateCell, history :- (List Nat), aliases :- Nat,
                 outside :- (List Nat), cap :- Nat]
              (PrivateExit.mk
                (PrivateAnswer.ok (privateRead cell)
                                  (privateCopies aliases (privateRead cell) history) outside) true))]
      [(bump tail)
       (fn [cell :- PrivateCell, history :- (List Nat), aliases :- Nat,
            outside :- (List Nat), cap :- Nat]
         (match (Nat.blt (privateRead cell) cap)
           [true (privateTarget tail (PrivateCell.mk (+ (privateRead cell) 1)) history aliases outside cap)]
           [false (PrivateExit.mk (PrivateAnswer.error 0 outside) true)]))]
      [(check ok tail)
       (fn [cell :- PrivateCell, history :- (List Nat), aliases :- Nat,
            outside :- (List Nat), cap :- Nat]
         (match ok
           [true (privateTarget tail cell history aliases outside cap)]
           [false (PrivateExit.mk (PrivateAnswer.error 1 outside) true)]))]
      [(alias tail)
       (fn [cell :- PrivateCell, history :- (List Nat), aliases :- Nat,
            outside :- (List Nat), cap :- Nat]
         (privateTarget tail cell history aliases outside cap))]
      [(retain tail)
       (fn [cell :- PrivateCell, history :- (List Nat), aliases :- Nat,
            outside :- (List Nat), cap :- Nat]
         (privateTarget tail cell history (+ aliases 1) outside cap))]
      [(branch condition left right)
       (fn [cell :- PrivateCell, history :- (List Nat), aliases :- Nat,
            outside :- (List Nat), cap :- Nat]
         (match condition
           [true (privateTarget left cell history aliases outside cap)]
           [false (privateTarget right cell history aliases outside cap)]))]))
  (a/theorem private-state-simulation [p :- PrivatePlan, safe :- (PrivateSafe p)]
    (forall [x :- Nat, history :- (List Nat), outside :- (List Nat), cap :- Nat]
      (= PrivateExit (privateTarget p (PrivateCell.mk x) history 0 outside cap)
         (PrivateExit.mk (privateSource p x history outside cap) true)))
    (induction safe)
    (all_goals (intro x) (intro history) (intro outside) (intro cap))
    (all_goals (simp only [privateTarget.eq_1 privateTarget.eq_2 privateTarget.eq_3
                          privateTarget.eq_4 privateTarget.eq_5 privateTarget.eq_6
                          privateSource.eq_1 privateSource.eq_2 privateSource.eq_3
                          privateSource.eq_4 privateSource.eq_5 privateSource.eq_6
                          privateRead.eq_1 privateCopies.eq_1]))
    (all_goals (try (rfl)))
    (all_goals (try (split_ifs)))
    (all_goals (try (rw [hc])))
    (all_goals (try (rfl)))
    (all_goals (try (first (exact (ih_h (+ x 1) history outside cap))
                           (exact (ih_h x history outside cap))
                           (exact (ih_hl x history outside cap))
                           (exact (ih_hr x history outside cap)))))
    (all_goals (try (rfl))))
  (a/theorem private-retain-rejected [tail :- PrivatePlan, h :- (PrivateSafe (PrivatePlan.retain tail))]
    False (cases h))
  (a/theorem private-branch-requires-both
    [b :- Bool, left :- PrivatePlan, right :- PrivatePlan,
     h :- (PrivateSafe (PrivatePlan.branch b left right))]
    (And (PrivateSafe left) (PrivateSafe right))
    (cases h) (constructor) (assumption) (assumption))
  (a/defn privateRepeat [n :- Nat] PrivatePlan
    (match n [zero PrivatePlan.done] [(succ previous) (PrivatePlan.bump (privateRepeat previous))]))
  (a/theorem private-repeat-safe [n :- Nat] (PrivateSafe (privateRepeat n))
    (induction n)
    (all_goals (simp only [privateRepeat.eq_1 privateRepeat.eq_2]))
    (all_goals (constructor))
    (all_goals (assumption)))
  (let [en (a/env)
        declaration (env/lookup en (nm/from-string "private-state-simulation"))
        goal (env/ci-type declaration) proof (env/ci-value declaration)]
    (doseq [name ["private-state-simulation" "private-retain-rejected"
                  "private-branch-requires-both" "private-repeat-safe"]
            :let [d (env/lookup en (nm/from-string name))]]
      (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
        (throw (ex-info "private-state proof failed independent kernel check" {:theorem name}))))
    {:environment en :goal goal :proof proof :goal-sha256 (k/expr-hash goal)
     :proof-sha256 (k/expr-hash proof)
     :trust :imported-init-statements :scope :finite-private-scalar-plans})))

(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))

(defn elaborate-plan
  "Reify actual finite input data into a kernel term. No claimed hash is used
   as the theorem proposition. Booleans select runtime branches, while safety
   evidence must cover both branches."
  [plan]
  (if (= :done plan) (k/c "PrivatePlan.done")
    (let [[op x y z] plan]
      (case op
        :bump (e/app (k/c "PrivatePlan.bump") (elaborate-plan x))
        :alias (e/app (k/c "PrivatePlan.alias") (elaborate-plan x))
        :retain (e/app (k/c "PrivatePlan.retain") (elaborate-plan x))
        :check (do (when-not (boolean? x) (throw (ex-info "check must be Boolean" {})))
                   (e/app* (k/c "PrivatePlan.check") (k/c (if x "Bool.true" "Bool.false"))
                           (elaborate-plan y)))
        :branch (do (when-not (boolean? x) (throw (ex-info "branch must be Boolean" {})))
                    (e/app* (k/c "PrivatePlan.branch") (k/c (if x "Bool.true" "Bool.false"))
                            (elaborate-plan y) (elaborate-plan z)))
        (throw (ex-info "unknown private plan operation" {:op op}))))))

(defn propose-safety [plan]
  (if (= :done plan) (k/c "PrivateSafe.done")
    (let [[op x y z] plan]
      (case op
        (:bump :alias)
        (when-let [p (propose-safety x)]
          (e/app* (k/c (if (= :bump op) "PrivateSafe.bump" "PrivateSafe.alias"))
                  (elaborate-plan x) p))
        :check (when-let [p (propose-safety y)]
                 (e/app* (k/c "PrivateSafe.check") (k/c (if x "Bool.true" "Bool.false"))
                         (elaborate-plan y) p))
        :branch (when-let [a (propose-safety y)]
                  (when-let [b (propose-safety z)]
                    (e/app* (k/c "PrivateSafe.branch") (k/c (if x "Bool.true" "Bool.false"))
                            (elaborate-plan y) (elaborate-plan z) a b)))
        nil))))

(defn check-plan [plan]
  (let [en (:environment @proof-state) term (elaborate-plan plan)
        goal (e/app (k/c "PrivateSafe") term) proof (propose-safety plan)]
    (if (and proof (env/verifies? en goal proof))
      {:status :accepted :term term :goal goal :proof proof
       :simulation (e/app* (k/c "private-state-simulation") term proof)}
      {:status :declined :reason :retained-version})))

(defn simulation-goal [plan]
  (let [[x h outside cap] (repeatedly 4 k/fvar!)
        [vx vh vo vc] (map e/fvar [x h outside cap])
        p (elaborate-plan plan)]
    (k/pi* [[x "value" k/Nat] [h "history" (k/List k/Nat)]
            [outside "outside" (k/List k/Nat)] [cap "cap" k/Nat]]
      (k/eq (k/c "PrivateExit")
            (e/app* (k/c "privateTarget") p (e/app (k/c "PrivateCell.mk") vx)
                    vh (e/lit-nat 0) vo vc)
            (e/app* (k/c "PrivateExit.mk")
                    (e/app* (k/c "privateSource") p vx vh vo vc) (k/c "Bool.true"))))))

(defn run-source [plan x history outside cap]
  (if (= :done plan) {:value x :history history :outside outside}
    (let [[op a b c] plan]
      (case op
        :bump (if (< x cap) (run-source a (inc x) history outside cap)
                  {:error :overflow :outside outside})
        :check (if a (run-source b x history outside cap)
                   {:error :check :outside outside})
        :alias (run-source a x history outside cap)
        :retain (run-source a x (cons x history) outside cap)
        :branch (run-source (if a b c) x history outside cap)))))

(defn run-target [plan x history aliases outside cap]
  (if (= :done plan)
    {:answer {:value x :history (concat (repeat aliases x) history) :outside outside} :released true}
    (let [[op a b c] plan]
      (case op
        :bump (if (< x cap) (run-target a (inc x) history aliases outside cap)
                  {:answer {:error :overflow :outside outside} :released true})
        :check (if a (run-target b x history aliases outside cap)
                   {:answer {:error :check :outside outside} :released true})
        :alias (run-target a x history aliases outside cap)
        :retain (run-target a x history (inc aliases) outside cap)
        :branch (run-target (if a b c) x history aliases outside cap)))))
