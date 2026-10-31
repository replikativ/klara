(ns klara.formal.checker
  "Soundness of the checker's head rules (spec/L4-compiler.md#checking).

  Each rewrite the checker applies at the head of a term is a step of the
  semantics. Since `step` is deterministic, a configuration and its step
  reach exactly the same terminal configurations (`step-equiv`). So two
  terms related by a chain of these rewrites cannot be told apart by
  running them.

  | Theorem          | Checker rule           |
  |------------------|------------------------|
  | beta-step        | L4.check.beta          |
  | fix-step         | L4.check.beta (recursive functions) |
  | let-value-step   | L4.check.let-value     |
  | if-true-step, if-false-step | L4.check.if-constant |
  | prim-step        | L4.check.prim          |
  | delta-step       | L4.check.delta (late links) |
  | pin-step         | L4.check.delta (pinned links) |
  | step-equiv       | composition of the above |

  Not proved here: rewriting under binders (the checker also compares
  function bodies, which needs contextual equivalence), L4.check.let-app,
  and the correspondence between named Core and Tm (the bridge, tested)."
  (:require [ansatz.core :as a]
            [klara.formal.core]
            [klara.formal.ws]
            [klara.formal.props]))

;; Simple values evaluate to themselves at level 0.
(a/theorem isVal-ev [w :- World, ws :- Worlds, n :- Nat, t :- Tm, h :- (= Bool (isVal t) Bool.true)]
  (= Out (ev w ws n 0 t) Out.val)
  (cases t)
  (all_goals (try (simp [isVal] at h)))
  (all_goals (simp [ev, atZero])))

;; ---------------------------------------------------------------------------
;; Head rules as steps

(a/theorem beta-step [w :- World, ws :- Worlds, n :- Nat, b :- Tm, v :- Tm, hv :- (= Bool (isVal v) Bool.true)]
  (Step (Config.mk w ws n (Tm.app (Tm.lam b) v)) (Config.mk w ws n (subst 0 v b)))
  (have rv (= Out (ev w ws n 0 v) Out.val)) (exact (isVal-ev w ws n v hv))
  (have r (= (Option Config) (step (Config.mk w ws n (Tm.app (Tm.lam b) v)))
             (Option.some Config (Config.mk w ws n (subst 0 v b)))))
  (simp only [step, run1, ev, atZero, seq2, beta]) (rw [rv]) (try (rfl))
  (exact (Step.mk _ _ r)))

(a/theorem fix-step [w :- World, ws :- Worlds, n :- Nat, fb :- Tm, v :- Tm, hv :- (= Bool (isVal v) Bool.true)]
  (Step (Config.mk w ws n (Tm.app (Tm.fix fb) v))
        (Config.mk w ws n (subst 0 v (subst 1 (Tm.fix fb) fb))))
  (have rv (= Out (ev w ws n 0 v) Out.val)) (exact (isVal-ev w ws n v hv))
  (have r (= (Option Config) (step (Config.mk w ws n (Tm.app (Tm.fix fb) v)))
             (Option.some Config (Config.mk w ws n (subst 0 v (subst 1 (Tm.fix fb) fb))))))
  (simp only [step, run1, ev, atZero, seq2, beta]) (rw [rv]) (try (rfl))
  (exact (Step.mk _ _ r)))

(a/theorem let-value-step [w :- World, ws :- Worlds, n :- Nat, v :- Tm, b :- Tm, hv :- (= Bool (isVal v) Bool.true)]
  (Step (Config.mk w ws n (Tm.let_ v b)) (Config.mk w ws n (subst 0 v b)))
  (have rv (= Out (ev w ws n 0 v) Out.val)) (exact (isVal-ev w ws n v hv))
  (have r (= (Option Config) (step (Config.mk w ws n (Tm.let_ v b)))
             (Option.some Config (Config.mk w ws n (subst 0 v b)))))
  (simp only [step, run1, ev, atZero, seq1]) (rw [rv]) (try (rfl))
  (exact (Step.mk _ _ r)))

(a/theorem if-true-step [w :- World, ws :- Worlds, n :- Nat, d :- Datum, u :- Tm, e :- Tm,
                         ht :- (= Bool (truthy (Tm.lit d)) Bool.true)]
  (Step (Config.mk w ws n (Tm.if_ (Tm.lit d) u e)) (Config.mk w ws n u))
  (have r (= (Option Config) (step (Config.mk w ws n (Tm.if_ (Tm.lit d) u e)))
             (Option.some Config (Config.mk w ws n u))))
  (simp only [step, run1, ev, atZero, seq1, pick]) (rw [ht]) (try (rfl))
  (exact (Step.mk _ _ r)))

(a/theorem if-false-step [w :- World, ws :- Worlds, n :- Nat, d :- Datum, u :- Tm, e :- Tm,
                          ht :- (= Bool (truthy (Tm.lit d)) Bool.false)]
  (Step (Config.mk w ws n (Tm.if_ (Tm.lit d) u e)) (Config.mk w ws n e))
  (have r (= (Option Config) (step (Config.mk w ws n (Tm.if_ (Tm.lit d) u e)))
             (Option.some Config (Config.mk w ws n e))))
  (simp only [step, run1, ev, atZero, seq1, pick]) (rw [ht]) (try (rfl))
  (exact (Step.mk _ _ r)))

(a/theorem prim-step [w :- World, ws :- Worlds, n :- Nat, op :- PrimOp, x :- Datum, y :- Datum, r :- Datum,
                      hr :- (= PrimRes (primApply op x y) (PrimRes.ok r))]
  (Step (Config.mk w ws n (Tm.prim op (Tm.lit x) (Tm.lit y))) (Config.mk w ws n (Tm.lit r)))
  (have rs (= (Option Config) (step (Config.mk w ws n (Tm.prim op (Tm.lit x) (Tm.lit y))))
              (Option.some Config (Config.mk w ws n (Tm.lit r)))))
  (simp only [step, run1, ev, atZero, seq2, primStep]) (rw [hr]) (try (rfl))
  (exact (Step.mk _ _ rs)))

(a/theorem delta-step [w :- World, ws :- Worlds, n :- Nat, id :- Nat, v :- Tm,
                       hl :- (= (Option Tm) (lookup w id) (Option.some Tm v))]
  (Step (Config.mk w ws n (Tm.glob id)) (Config.mk w ws n v))
  (have rs (= (Option Config) (step (Config.mk w ws n (Tm.glob id))) (Option.some Config (Config.mk w ws n v))))
  (simp only [step, run1, ev, atZero]) (rw [hl]) (try (rfl))
  (exact (Step.mk _ _ rs)))

(a/theorem pin-step [w :- World, ws :- Worlds, n :- Nat, wi :- Nat, id :- Nat, wv :- World, v :- Tm,
                     hw :- (= (Option World) (worldAt ws wi) (Option.some World wv)),
                     hl :- (= (Option Tm) (lookup wv id) (Option.some Tm v))]
  (Step (Config.mk w ws n (Tm.pin wi id)) (Config.mk w ws n (pinTm wi v)))
  (have rs (= (Option Config) (step (Config.mk w ws n (Tm.pin wi id)))
              (Option.some Config (Config.mk w ws n (pinTm wi v)))))
  (simp only [step, run1, ev, atZero, pinResult]) (rw [hw]) (simp only [pinValue]) (rw [hl]) (try (rfl))
  (exact (Step.mk _ _ rs)))

;; ---------------------------------------------------------------------------
;; A step preserves the set of terminal configurations reached.

(a/theorem star-det [c :- Config, c1 :- Config, c3 :- Config, hs :- (Star c c3),
                     ht :- (forall [d :- Config] (Not (Step c3 d))), h1 :- (Step c c1)]
  (Star c1 c3)
  (cases hs :with
    [(refl x) (exfalso) (exact (ht c1 h1))]
    [(step x y z hxy hyz) (have he (= Config c1 y)) (exact (step-det x c1 y h1 hxy)) (rw [he]) (exact hyz)]))

(a/theorem step-equiv [c :- Config, c1 :- Config, d :- Config, h1 :- (Step c c1),
                       ht :- (forall [e :- Config] (Not (Step d e)))]
  (And (=> (Star c d) (Star c1 d)) (=> (Star c1 d) (Star c d)))
  (constructor)
  (intro hs) (exact (star-det c c1 d hs ht h1))
  (intro hs) (exact (Star.step c c1 d h1 hs)))

;; ---------------------------------------------------------------------------
;; Joining: configurations that reach a common configuration reach the same
;; terminal configurations. Used by proof-carrying candidates (L4.check.certificate).

(a/theorem star-equiv [c :- Config, m :- Config, hm :- (Star c m)]
  (forall [d :- Config] (=> (forall [e :- Config] (Not (Step d e)))
                            (And (=> (Star c d) (Star m d)) (=> (Star m d) (Star c d)))))
  (induction hm)
  (all_goals (intro d) (intro ht) (constructor))
  (intro hx) (exact hx)
  (intro hx) (exact hx)
  (intro hx) (exact (And.left (ih_hs d ht) (star-det _ _ d hx ht h)))
  (intro hx) (exact (Star.step _ _ d h (And.right (ih_hs d ht) hx))))

(a/theorem equiv-of-reach [c :- Config, c2 :- Config, m :- Config, h1 :- (Star c m), h2 :- (Star c2 m)]
  (forall [d :- Config] (=> (forall [e :- Config] (Not (Step d e)))
                            (And (=> (Star c d) (Star c2 d)) (=> (Star c2 d) (Star c d)))))
  (intro d) (intro ht) (constructor)
  (intro hs) (exact (And.right (star-equiv c2 m h2 d ht) (And.left (star-equiv c m h1 d ht) hs)))
  (intro hs) (exact (And.right (star-equiv c m h1 d ht) (And.left (star-equiv c2 m h2 d ht) hs))))

;; Running an integer literal through checked arithmetic.
(a/theorem checked-in-range [i :- Int, hi :- (= Bool (inRange i) Bool.true)]
  (= PrimRes (checked i) (PrimRes.ok (Datum.int i)))
  (simp only [checked]) (rw [hi]))

;; Building blocks for certificates: one reduction step, with the reduced
;; term given explicitly (the elaborator does not unfold subst when unifying).
(a/theorem reach-beta [w :- World, ws :- Worlds, n :- Nat, b :- Tm, v :- Tm, b2 :- Tm, m :- Config,
                       hv :- (= Bool (isVal v) Bool.true), he :- (= Tm (subst 0 v b) b2),
                       hm :- (Star (Config.mk w ws n b2) m)]
  (Star (Config.mk w ws n (Tm.app (Tm.lam b) v)) m)
  (have h1 (Step (Config.mk w ws n (Tm.app (Tm.lam b) v)) (Config.mk w ws n (subst 0 v b))))
  (exact (beta-step w ws n b v hv))
  (rw [he] at h1)
  (exact (Star.step _ _ _ h1 hm)))

(a/theorem reach-prim [w :- World, ws :- Worlds, n :- Nat, op :- PrimOp, x :- Datum, y :- Datum, r :- Datum, m :- Config,
                       hr :- (= PrimRes (primApply op x y) (PrimRes.ok r)),
                       hm :- (Star (Config.mk w ws n (Tm.lit r)) m)]
  (Star (Config.mk w ws n (Tm.prim op (Tm.lit x) (Tm.lit y))) m)
  (exact (Star.step _ _ _ (prim-step w ws n op x y r hr) hm)))
