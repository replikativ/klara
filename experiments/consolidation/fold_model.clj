(ns consolidation.fold-model
  "A reusable finite-fold/private-cell simulation. Actual core lowering and
   array representation are tested bridges, not consequences of this model."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [klara.fusion :as fusion]
            [klara.fusion.kernel :as k]
            [klara.core :as c]
            [proof-staging :as ps]))

(defn prove! []
  (binding [*ns* (the-ns 'consolidation.fold-model)]
    (reset! a/ansatz-env @ps/proof-state)
    (a/inductive FoldCell [] (mk [value Nat]))
    (a/inductive FoldAnswer [] (ok [value Nat] [outside (List Nat)]) (error [outside (List Nat)]))
    (a/inductive FoldExit [] (mk [answer FoldAnswer] [released Bool]))
    (a/defn foldRead [cell :- FoldCell] Nat (match cell [(mk value) value]))
    (a/defn foldSource [xs :- (List Nat)]
      (=> Nat (=> (=> Nat (=> Nat (Option Nat))) (=> (List Nat) FoldAnswer)))
      (match xs
        [nil (fn [state :- Nat, step :- (=> Nat (=> Nat (Option Nat))), outside :- (List Nat)]
               (FoldAnswer.ok state outside))]
        [(cons x rest)
         (fn [state :- Nat, step :- (=> Nat (=> Nat (Option Nat))), outside :- (List Nat)]
           (match (step state x)
             [none (FoldAnswer.error outside)]
             [(some next) (foldSource rest next step outside)]))]))
    (a/defn foldTarget [xs :- (List Nat)]
      (=> FoldCell (=> (=> Nat (=> Nat (Option Nat))) (=> (List Nat) FoldExit)))
      (match xs
        [nil (fn [cell :- FoldCell, step :- (=> Nat (=> Nat (Option Nat))), outside :- (List Nat)]
               (FoldExit.mk (FoldAnswer.ok (foldRead cell) outside) true))]
        [(cons x rest)
         (fn [cell :- FoldCell, step :- (=> Nat (=> Nat (Option Nat))), outside :- (List Nat)]
           (match (step (foldRead cell) x)
             [none (FoldExit.mk (FoldAnswer.error outside) true)]
             [(some next) (foldTarget rest (FoldCell.mk next) step outside)]))]))
    (a/theorem fold-step-refinement
      [r :- (Option Nat), rest :- (List Nat),
       f :- (=> Nat (=> Nat (Option Nat))), g :- (=> Nat (=> Nat (Option Nat))),
       outside :- (List Nat),
       ih :- (forall [next :- Nat]
               (= FoldExit (foldTarget rest (FoldCell.mk next) g outside)
                  (FoldExit.mk (foldSource rest next f outside) true)))]
      (= FoldExit
         (match r [none (FoldExit.mk (FoldAnswer.error outside) true)]
                  [(some next) (foldTarget rest (FoldCell.mk next) g outside)])
         (FoldExit.mk (match r [none (FoldAnswer.error outside)]
                              [(some next) (foldSource rest next f outside)]) true))
      (cases r)
      (all_goals (try (rfl)))
      (all_goals (exact (ih _))))
    (a/theorem fold-private-refinement
      [xs :- (List Nat), f :- (=> Nat (=> Nat (Option Nat))), g :- (=> Nat (=> Nat (Option Nat))),
       h :- (forall [state :- Nat, x :- Nat] (= (Option Nat) (f state x) (g state x)))]
      (forall [state :- Nat, outside :- (List Nat)]
        (= FoldExit (foldTarget xs (FoldCell.mk state) g outside)
           (FoldExit.mk (foldSource xs state f outside) true)))
      (induction xs)
      (all_goals (intro state) (intro outside))
      (all_goals (simp only [foldTarget.eq_1 foldTarget.eq_2 foldSource.eq_1 foldSource.eq_2 foldRead.eq_1]))
      (all_goals (try (rw [(foldRead.eq_1 state)])))
      (all_goals (try (rw [(h state head)])))
      (all_goals (exact (fold-step-refinement (g state head) tail f g outside
                         (fn [next :- Nat] (ih_tail next outside))))))
    (a/theorem fold-total-source
      [xs :- (List Nat), f :- (=> Nat (=> Nat Nat))]
      (forall [state :- Nat, outside :- (List Nat)]
        (= FoldAnswer
           (foldSource xs state (fn [a :- Nat, x :- Nat] (Option.some Nat (f a x))) outside)
           (FoldAnswer.ok (List.foldl f state xs) outside)))
      (induction xs)
      (all_goals (intro state) (intro outside))
      (all_goals (simp only [foldSource.eq_1 foldSource.eq_2]))
      (all_goals (try (rfl)))
      (all_goals (exact (ih_tail (f state head) outside))))
    (a/inductive FoldBound [] :in Prop :indices [f (=> Nat Nat), upper Nat, xs (List Nat)]
      (nil [f (=> Nat Nat)] [upper Nat] :where [f upper (List.nil Nat)])
      (cons [f (=> Nat Nat)] [upper Nat] [x Nat] [rest (List Nat)]
            [hx (Nat.le (f x) upper)] [hr (FoldBound f upper rest)]
            :where [f upper (List.cons Nat x rest)]))
    (a/theorem fold-add-bound
      [acc :- Nat, value :- Nat, size :- Nat, upper :- Nat, hv :- (<= value upper)]
      (<= (+ (+ acc value) (* size upper)) (+ acc (* (Nat.succ size) upper)))
      (rw Nat.succ_mul) (omega))
    (a/theorem fold-sum-bound
      [f :- (=> Nat Nat), upper :- Nat, xs :- (List Nat), h :- (FoldBound f upper xs)]
      (forall [acc :- Nat]
        (<= (List.foldl (fn [a :- Nat, x :- Nat] (+ a (f x))) acc xs)
            (+ acc (* (List.length xs) upper))))
      (induction h)
      (all_goals (intro acc))
      (all_goals (simp only [List.length_nil Nat.zero_mul Nat.add_zero]))
      (all_goals (try (rw [(Nat.zero_mul upper) (Nat.add_zero acc)])))
      (all_goals (try (exact (Nat.le_refl acc))))
      (all_goals (exact (Nat.le_trans (ih_hr (+ acc (f x)))
                          (fold-add-bound acc (f x) (List.length rest) upper hx)))))
    (let [en (a/env)]
      (doseq [name ["fold-step-refinement" "fold-private-refinement" "fold-total-source" "fold-sum-bound"]
              :let [d (env/lookup en (nm/from-string name))]]
        (when-not (env/verifies? en (env/ci-type d) (env/ci-value d))
          (throw (ex-info "fold model theorem failed independent check" {:theorem name}))))
      en)))

(def proof-state (delay (binding [*out* (java.io.StringWriter.)] (prove!))))

(defn witness
  "Compose the actual mathematical edge with finite private refinement.
   Bounds are a separate mandatory obligation for successful Long execution."
  [edge]
  (let [en @proof-state
        el (fusion/elaborate {:claim fusion/supported-claim :resolve-def (constantly nil)}
                             (ps/core-term (:to edge)))
        _ (when (seq (:chain el))
            (throw (ex-info "private residual requires an already fused fold" {:reason :unfused})))
        f (get-in el [:fold :f]) init (get-in el [:fold :init])
        [a x xs outside value] (repeatedly 5 k/fvar!)
        vx (e/fvar xs) vo (e/fvar outside) exit (k/c "FoldExit") answer (k/c "FoldAnswer")
        step (k/lam* [[a "acc" k/Nat] [x "x" k/Nat]]
                     (e/app* (k/c "Option.some" [k/l0]) k/Nat (e/app* f (e/fvar a) (e/fvar x))))
        option (e/app (k/c "Option" [k/l0]) k/Nat)
        reflexive (k/lam* [[a "acc" k/Nat] [x "x" k/Nat]]
                         (e/app* (k/c "Eq.refl" [k/l1]) option (e/app* step (e/fvar a) (e/fvar x))))
        target (e/app* (k/c "foldTarget") vx (e/app (k/c "FoldCell.mk") init) step vo)
        mid-answer (e/app* (k/c "foldSource") vx init step vo)
        release (fn [v] (e/app* (k/c "FoldExit.mk") v (k/c "Bool.true")))
        finish (fn [v] (release (e/app* (k/c "FoldAnswer.ok") v vo)))
        scalar-target (k/foldl k/Nat k/Nat f init vx)
        scalar-source (ps/meaning (:from edge) xs)
        private-proof (e/app* (k/c "fold-private-refinement") vx step step reflexive init vo)
        total-proof (e/app* (k/c "fold-total-source") vx f init vo)
        congr (fn [ty left right fun proof]
                (e/app* (k/c "congrArg" [k/l1 k/l1]) ty exit left right fun proof))
        total-exit (congr answer mid-answer (e/app* (k/c "FoldAnswer.ok") scalar-target vo)
                          (k/lam* [[value "answer" answer]] (release (e/fvar value))) total-proof)
        math-proof (e/app* (k/c "Eq.symm" [k/l1]) k/Nat scalar-source scalar-target
                           (e/app (:proof edge) vx))
        math-exit (congr k/Nat scalar-target scalar-source
                         (k/lam* [[value "result" k/Nat]] (finish (e/fvar value))) math-proof)
        trans (fn [left mid right p q] (e/app* (k/c "Eq.trans" [k/l1]) exit left mid right p q))
        proof (k/lam* [[xs "xs" (k/List k/Nat)] [outside "outside" (k/List k/Nat)]]
                      (trans target (release mid-answer) (finish scalar-source) private-proof
                             (trans (release mid-answer) (finish scalar-target) (finish scalar-source) total-exit math-exit)))
        goal (k/pi* [[xs "xs" (k/List k/Nat)] [outside "outside" (k/List k/Nat)]]
                     (k/eq exit target (finish scalar-source)))]
    (when-not (env/verifies? en goal proof)
      (throw (ex-info "private mathematical composition proof rejected" {:reason :private-proof})))
    {:source-id (:source-id edge) :target-id (:target-id edge)
     :goal goal :proof proof :goal-sha256 (k/expr-hash goal) :proof-sha256 (k/expr-hash proof)}))

(defn verify-witness? [edge receipt]
  (try
    (let [expected (witness edge)]
      (and (= (:source-id expected) (:source-id receipt)) (= (:target-id expected) (:target-id receipt))
           (= (:goal expected) (:goal receipt))
           (env/verifies? @proof-state (:goal expected) (:proof receipt))))
    (catch Exception _ false)))
