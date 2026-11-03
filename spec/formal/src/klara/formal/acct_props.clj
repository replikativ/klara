(ns klara.formal.acct-props
  "Conservation in λ-acct (L3.account.conservation): every step of every
  term, typed or not, keeps minted = wallet + spent + held in live tokens.
  Only the token operations change the store, and each is a balanced
  transfer; raising, catching, handling and resuming (any number of times)
  leave it alone, so copying a continuation cannot create authority.

  The headline theorem is `Acct.conservation`."
  (:require [ansatz.core :as a]
            [klara.formal.acct]))

;; ---------------------------------------------------------------------------
;; The live list

(a/theorem Acct.find-total [l :- Acct.Live]
  (forall [i :- Nat] (forall [m :- Nat]
    (=> (= (Option Nat) (Acct.find l i) (Option.some Nat m))
        (= Nat (+ (Acct.total (Acct.remove l i)) m) (Acct.total l)))))
  (induction l)
  (all_goals (intro i) (intro m) (intro h))
  (simp [Acct.find] at h)
  (revert h)
  (simp only [Acct.find, Acct.remove, Acct.total])
  (split)
  (all_goals (dsimp) (intro h2))
  (all_goals (simp only [h, Acct.total]))
  (cases h2) (omega)
  (have ih2 (= Nat (+ (Acct.total (Acct.remove rest i)) m) (Acct.total rest))) (exact (ih_rest i m h2))
  (omega))

(a/theorem Acct.beq-ne [a :- Nat, b :- Nat, h :- (Not (= Nat a b))] (= Bool (Nat.beq a b) Bool.false)
  (cases hq (Nat.beq a b)) (rfl) (exfalso) (apply h) (simp_all [Nat.beq_eq]))

(a/theorem Acct.find-remove-ne [l :- Acct.Live]
  (forall [i :- Nat] (forall [j :- Nat]
    (=> (Not (= Nat i j)) (= (Option Nat) (Acct.find (Acct.remove l i) j) (Acct.find l j)))))
  (induction l)
  (all_goals (intro i) (intro j) (intro hne))
  (simp [Acct.remove, Acct.find])
  (simp only [Acct.remove])
  (split)
  (all_goals (simp_all [Acct.find]))
  (rw [(Acct.beq-ne _ _ hne)]))

;; ---------------------------------------------------------------------------
;; Outcomes that conserve: a step leaves minted unchanged.

(a/inductive Acct.CO [] :in Prop :indices [s Acct.Store o Acct.Out]
  (val [s Acct.Store] :where [s Acct.Out.val])
  (next [s Acct.Store] [s2 Acct.Store] [e Acct.Tm] [h (= Nat (Acct.minted s2) (Acct.minted s))]
        :where [s (Acct.Out.next s2 e)])
  (eff [s Acct.Store] [op Nat] [v Acct.Tm] [k Acct.Tm] :where [s (Acct.Out.eff op v k)])
  (exn [s Acct.Store] [v Acct.Tm] :where [s (Acct.Out.exn v)])
  (stuck [s Acct.Store] [st Acct.Stuck] :where [s (Acct.Out.stuck st)]))

(a/theorem Acct.co-same [s :- Acct.Store, e :- Acct.Tm] (Acct.CO s (Acct.Out.next s e))
  (apply Acct.CO.next) (rfl))

(a/theorem Acct.co-stuck [s :- Acct.Store, st :- Acct.Stuck] (Acct.CO s (Acct.Out.stuck st))
  (exact (Acct.CO.stuck s st)))

(a/theorem Acct.frame-co [s :- Acct.Store, o :- Acct.Out, fr :- (=> Acct.Tm Acct.Tm), ho :- (Acct.CO s o)]
  (Acct.CO s (Acct.frame o fr))
  (cases ho)
  (all_goals (simp [Acct.frame]))
  (all_goals (constructor))
  (all_goals (assumption)))

(a/theorem Acct.seq1-co [s :- Acct.Store, o :- Acct.Out, fr :- (=> Acct.Tm Acct.Tm), d :- Acct.Out,
                         ho :- (Acct.CO s o), hd :- (Acct.CO s d)]
  (Acct.CO s (Acct.seq1 o fr d))
  (cases ho)
  (all_goals (simp [Acct.seq1, Acct.frame]))
  (all_goals (try (assumption)))
  (all_goals (constructor))
  (all_goals (assumption)))

(a/theorem Acct.seq2-co [s :- Acct.Store, o1 :- Acct.Out, o2 :- Acct.Out, fr1 :- (=> Acct.Tm Acct.Tm),
                         fr2 :- (=> Acct.Tm Acct.Tm), d :- Acct.Out,
                         h1 :- (Acct.CO s o1), h2 :- (Acct.CO s o2), hd :- (Acct.CO s d)]
  (Acct.CO s (Acct.seq2 o1 o2 fr1 fr2 d))
  (cases h1)
  (all_goals (simp [Acct.seq2, Acct.frame]))
  (cases h2)
  (all_goals (simp [Acct.frame]))
  (all_goals (try (assumption)))
  (all_goals (constructor))
  (all_goals (assumption)))

(a/theorem Acct.beta-co [s :- Acct.Store, f :- Acct.Tm, x :- Acct.Tm] (Acct.CO s (Acct.beta s f x))
  (cases f)
  (all_goals (simp [Acct.beta]))
  (all_goals (first (apply Acct.co-same) (apply Acct.co-stuck))))

;; The token operations are balanced transfers.

(a/theorem Acct.takeN-co [s :- Acct.Store, n :- Nat] (Acct.CO s (Acct.takeN s n))
  (cases s)
  (simp only [Acct.takeN])
  (split)
  (all_goals (try (apply Acct.co-stuck)))
  (apply Acct.CO.next)
  (simp_all [Acct.minted, Acct.total, Nat.ble_eq])
  (omega))

(a/theorem Acct.takeStep-co [s :- Acct.Store, x :- Acct.Tm] (Acct.CO s (Acct.takeStep s x))
  (simp only [Acct.takeStep])
  (split)
  (apply Acct.co-stuck)
  (apply Acct.takeN-co))

(a/theorem Acct.spendH-co [w :- Nat, sp :- Nat, nx :- Nat, l :- Acct.Live, i :- Nat, n :- Nat, h :- (Option Nat),
                           hh :- (forall [m :- Nat] (=> (= (Option Nat) h (Option.some Nat m))
                                                        (= (Option Nat) (Acct.find l i) (Option.some Nat m))))]
  (Acct.CO (Acct.Store.mk w sp nx l) (Acct.spendH (Acct.Store.mk w sp nx l) i n h))
  (cases h)
  (simp [Acct.spendH]) (apply Acct.co-stuck)
  (simp only [Acct.spendH])
  (split)
  (all_goals (try (apply Acct.co-stuck)))
  (apply Acct.CO.next)
  (have hf (= (Option Nat) (Acct.find l i) (Option.some Nat val))) (exact (hh val (Eq.refl (Option.some Nat val))))
  (have ht (= Nat (+ (Acct.total (Acct.remove l i)) val) (Acct.total l))) (exact (Acct.find-total l i val hf))
  (simp_all [Acct.minted, Acct.total, Nat.ble_eq])
  (omega))

(a/theorem Acct.held-true [l :- Acct.Live, i :- Nat, m :- Nat,
                           h :- (= (Option Nat) (Acct.held true l i) (Option.some Nat m))]
  (= (Option Nat) (Acct.find l i) (Option.some Nat m))
  (simp [Acct.held] at h) (exact h))

(a/theorem Acct.spendStep-co [s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm] (Acct.CO s (Acct.spendStep true s u x))
  (cases u)
  (all_goals (simp only [Acct.spendStep]))
  (all_goals (try (apply Acct.co-stuck)))
  (simp only [Acct.spendN])
  (split)
  (apply Acct.co-stuck)
  (cases s)
  (simp only)
  (apply Acct.spendH-co)
  (intro m) (intro hm) (exact hm))

(a/theorem Acct.joinH-co [w :- Nat, sp :- Nat, nx :- Nat, l :- Acct.Live, i :- Nat, j :- Nat, hne :- (Not (= Nat i j)),
                          h1 :- (Option Nat), h2 :- (Option Nat),
                          hh1 :- (forall [m :- Nat] (=> (= (Option Nat) h1 (Option.some Nat m))
                                                         (= (Option Nat) (Acct.find l i) (Option.some Nat m)))),
                          hh2 :- (forall [m :- Nat] (=> (= (Option Nat) h2 (Option.some Nat m))
                                                         (= (Option Nat) (Acct.find l j) (Option.some Nat m))))]
  (Acct.CO (Acct.Store.mk w sp nx l) (Acct.joinH (Acct.Store.mk w sp nx l) i j h1 h2))
  (cases h1 :with
    [(none) (simp [Acct.joinH]) (apply Acct.co-stuck)]
    [(some m1)
       (cases h2 :with
         [(none) (simp [Acct.joinH]) (apply Acct.co-stuck)]
         [(some m2)
            (simp only [Acct.joinH])
            (apply Acct.CO.next)
            (have f1 (= (Option Nat) (Acct.find l i) (Option.some Nat m1))) (exact (hh1 m1 (Eq.refl (Option.some Nat m1))))
            (have f2 (= (Option Nat) (Acct.find l j) (Option.some Nat m2))) (exact (hh2 m2 (Eq.refl (Option.some Nat m2))))
            (have f2r (= (Option Nat) (Acct.find (Acct.remove l i) j) (Option.some Nat m2)))
            (rw [(Acct.find-remove-ne l i j hne)]) (exact f2)
            (have t1 (= Nat (+ (Acct.total (Acct.remove l i)) m1) (Acct.total l))) (exact (Acct.find-total l i m1 f1))
            (have t2 (= Nat (+ (Acct.total (Acct.remove (Acct.remove l i) j)) m2) (Acct.total (Acct.remove l i))))
            (exact (Acct.find-total (Acct.remove l i) j m2 f2r))
            (simp_all [Acct.minted, Acct.total])
            (omega)])]))

(a/theorem Acct.joinStep-co [s :- Acct.Store, u :- Acct.Tm, v :- Acct.Tm] (Acct.CO s (Acct.joinStep true s u v))
  (cases u)
  (all_goals (simp only [Acct.joinStep]))
  (all_goals (try (apply Acct.co-stuck)))
  (cases v)
  (all_goals (simp only))
  (all_goals (try (apply Acct.co-stuck)))
  (simp only [Acct.joinN])
  (split)
  (apply Acct.co-stuck)
  (cases s)
  (simp only)
  (apply Acct.joinH-co)
  (intro he) (subst he) (simp_all [Nat.beq_eq])
  (all_goals (intro m) (intro hm) (exact hm)))

(a/theorem Acct.putH-co [w :- Nat, sp :- Nat, nx :- Nat, l :- Acct.Live, i :- Nat, h :- (Option Nat),
                         hh :- (forall [m :- Nat] (=> (= (Option Nat) h (Option.some Nat m))
                                                      (= (Option Nat) (Acct.find l i) (Option.some Nat m))))]
  (Acct.CO (Acct.Store.mk w sp nx l) (Acct.putH (Acct.Store.mk w sp nx l) i h))
  (cases h)
  (simp [Acct.putH]) (apply Acct.co-stuck)
  (simp only [Acct.putH])
  (apply Acct.CO.next)
  (have hf (= (Option Nat) (Acct.find l i) (Option.some Nat val))) (exact (hh val (Eq.refl (Option.some Nat val))))
  (have ht (= Nat (+ (Acct.total (Acct.remove l i)) val) (Acct.total l))) (exact (Acct.find-total l i val hf))
  (simp_all [Acct.minted])
  (omega))

(a/theorem Acct.putStep-co [s :- Acct.Store, u :- Acct.Tm] (Acct.CO s (Acct.putStep true s u))
  (cases u)
  (all_goals (simp only [Acct.putStep]))
  (all_goals (try (apply Acct.co-stuck)))
  (cases s)
  (simp only)
  (apply Acct.putH-co)
  (intro m) (intro hm) (exact hm))

;; Catching and handling pass steps through and otherwise do not touch the store.

(a/theorem Acct.tryOut-co [s :- Acct.Store, h :- Acct.Tm, o :- Acct.Out, b :- Acct.Tm, ho :- (Acct.CO s o)]
  (Acct.CO s (Acct.tryOut s h o b))
  (cases ho)
  (all_goals (simp [Acct.tryOut]))
  (all_goals (first (apply Acct.co-same) (constructor)))
  (all_goals (assumption)))

(a/theorem Acct.handleEff-co [s :- Acct.Store, ops :- (List Nat), r :- Acct.Tm, o :- Acct.Tm, op :- Nat,
                              v :- Acct.Tm, k :- Acct.Tm]
  (Acct.CO s (Acct.handleEff s ops r o op v k))
  (simp only [Acct.handleEff])
  (split)
  (apply Acct.co-same)
  (constructor))

(a/theorem Acct.handlingOut-co [s :- Acct.Store, ops :- (List Nat), r :- Acct.Tm, o :- Acct.Tm, ob :- Acct.Out,
                                b :- Acct.Tm, ho :- (Acct.CO s ob)]
  (Acct.CO s (Acct.handlingOut s ops r o ob b))
  (cases ho)
  (all_goals (simp [Acct.handlingOut]))
  (all_goals (first (apply Acct.co-same) (apply Acct.handleEff-co) (constructor)))
  (all_goals (assumption)))

(a/theorem Acct.ev-co [t :- Acct.Tm]
  (forall [s :- Acct.Store] (Acct.CO s (Acct.ev true s t)))
  (induction t)
  (all_goals (intro s))
  (all_goals (simp only [Acct.ev]))
  (all_goals (try (first (apply Acct.co-stuck) (constructor))))
  (all_goals (try (first (apply Acct.seq2-co) (apply Acct.seq1-co) (apply Acct.tryOut-co)
                         (apply Acct.handlingOut-co) (apply Acct.co-same))))
  (all_goals (try (first (apply ih_f) (apply ih_x) (apply ih_e) (apply ih_c) (apply ih_u) (apply ih_v)
                         (apply ih_b) (apply Acct.beta-co) (apply Acct.co-same) (apply Acct.takeStep-co)
                         (apply Acct.spendStep-co) (apply Acct.joinStep-co) (apply Acct.putStep-co)
                         (constructor)))))

;; Every step keeps minted = wallet + spent + held (L3.account.conservation).
(a/theorem Acct.co-stepOut [s :- Acct.Store, o :- Acct.Out, s2 :- Acct.Store, t2 :- Acct.Tm, ho :- (Acct.CO s o),
                            h :- (= (Option Acct.Config) (Acct.stepOut o) (Option.some Acct.Config (Acct.Config.mk s2 t2)))]
  (= Nat (Acct.minted s2) (Acct.minted s))
  (cases ho)
  (all_goals (simp [Acct.stepOut] at h))
  (all_goals (cases h))
  (assumption))

(a/theorem Acct.conservation [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm,
                              h :- (= (Option Acct.Config) (Acct.step (Acct.Config.mk s t))
                                      (Option.some Acct.Config (Acct.Config.mk s2 t2)))]
  (= Nat (Acct.minted s2) (Acct.minted s))
  (simp only [Acct.step] at h)
  (exact (Acct.co-stepOut s (Acct.ev true s t) s2 t2 (Acct.ev-co t s) h)))
