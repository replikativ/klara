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
    [(step x y z hxy hyz) (have he (= Config c1 y)) (exact (step-det c c1 y h1 hxy)) (rw [he]) (exact hyz)]))

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

;; Checked arithmetic that stays in range: a multiplication or addition of
;; integers whose result is a 64-bit value succeeds with that value.
(a/theorem prim-mul-ok [a :- Int, b :- Int, h :- (= Bool (inRange (* a b)) Bool.true)]
  (= PrimRes (primApply PrimOp.mul (Datum.int a) (Datum.int b)) (PrimRes.ok (Datum.int (* a b))))
  (simp only [primApply, intOp]) (exact (checked-in-range (* a b) h)))

(a/theorem prim-add-ok [a :- Int, b :- Int, h :- (= Bool (inRange (+ a b)) Bool.true)]
  (= PrimRes (primApply PrimOp.add (Datum.int a) (Datum.int b)) (PrimRes.ok (Datum.int (+ a b))))
  (simp only [primApply, intOp]) (exact (checked-in-range (+ a b) h)))

;; A value between the 64-bit bounds is in range (bounds from nlinarith).
(a/theorem in-range [x :- Int, h1 :- (<= (Int.negSucc 9223372036854775807) x), h2 :- (<= x (Int.ofNat 9223372036854775807))]
  (= Bool (inRange x) Bool.true)
  (simp only [inRange]) (unfold minLong) (unfold maxLong) (simp)
  (apply And.intro) (apply (Iff.mpr Int.not_lt)) (exact h1) (apply (Iff.mpr Int.not_lt)) (exact h2))

;; Evaluation inside arithmetic: a step of a nested prim is a step of the
;; operand it is in (left first, then right once the left is a literal). With
;; ev-prim-lit and step-of-ev, a certificate for straight-line integer code
;; is a chain of these lemmas, one per operation (design/07-performance.md).
(a/theorem ev-prim-lit [w :- World, ws :- Worlds, n :- Nat, op :- PrimOp, x :- Datum, y :- Datum, r :- Datum,
                        hr :- (= PrimRes (primApply op x y) (PrimRes.ok r))]
  (= Out (ev w ws n 0 (Tm.prim op (Tm.lit x) (Tm.lit y))) (Out.next n (Tm.lit r)))
  (simp only [ev, seq2, atZero, primStep]) (rw [hr]) (try (rfl)))

(a/theorem ev-prim-l [w :- World, ws :- Worlds, n :- Nat, n2 :- Nat, op :- PrimOp, x :- Tm, x2 :- Tm, y :- Tm,
                      hx :- (= Out (ev w ws n 0 x) (Out.next n2 x2))]
  (= Out (ev w ws n 0 (Tm.prim op x y)) (Out.next n2 (Tm.prim op x2 y)))
  (simp only [ev, seq2, hx, frame]) (try (rfl)))

(a/theorem ev-prim-r [w :- World, ws :- Worlds, n :- Nat, n2 :- Nat, op :- PrimOp, d :- Datum, y :- Tm, y2 :- Tm,
                      hy :- (= Out (ev w ws n 0 y) (Out.next n2 y2))]
  (= Out (ev w ws n 0 (Tm.prim op (Tm.lit d) y)) (Out.next n2 (Tm.prim op (Tm.lit d) y2)))
  (simp only [ev, seq2, hy, frame]) (try (rfl)))

(a/theorem step-of-ev [w :- World, ws :- Worlds, n :- Nat, n2 :- Nat, t :- Tm, t2 :- Tm,
                       h :- (= Out (ev w ws n 0 t) (Out.next n2 t2))]
  (Step (Config.mk w ws n t) (Config.mk w ws n2 t2))
  (have r (= (Option Config) (step (Config.mk w ws n t)) (Option.some Config (Config.mk w ws n2 t2))))
  (simp only [step, run1, h, stepOut]) (try (rfl))
  (exact (Step.mk _ _ r)))

;; ---------------------------------------------------------------------------
;; Speculation (L4.check.speculate): `(if g a r)` means `r` when `a` does,
;; whatever the guard's value. On the implementation side the guard must be
;; a total pure predicate, so that evaluating it reaches a literal.

(a/theorem speculate-sound [w :- World, ws :- Worlds, n :- Nat, d :- Datum, sa :- Tm, r :- Tm,
                            ha :- (forall [e :- Config] (=> (forall [f :- Config] (Not (Step e f)))
                                    (And (=> (Star (Config.mk w ws n sa) e) (Star (Config.mk w ws n r) e))
                                         (=> (Star (Config.mk w ws n r) e) (Star (Config.mk w ws n sa) e)))))]
  (forall [e :- Config] (=> (forall [f :- Config] (Not (Step e f)))
    (And (=> (Star (Config.mk w ws n (Tm.if_ (Tm.lit d) sa r)) e) (Star (Config.mk w ws n r) e))
         (=> (Star (Config.mk w ws n r) e) (Star (Config.mk w ws n (Tm.if_ (Tm.lit d) sa r)) e)))))
  (intro e) (intro ht)
  (cases hb (truthy (Tm.lit d)))
  ;; the guard is false: the speculation steps to the reference
  (have hs (Step (Config.mk w ws n (Tm.if_ (Tm.lit d) sa r)) (Config.mk w ws n r)))
  (exact (if-false-step w ws n d sa r hb))
  (exact (step-equiv _ _ e hs ht))
  ;; the guard is true: it steps to the specialized branch, which means the reference
  (have hs (Step (Config.mk w ws n (Tm.if_ (Tm.lit d) sa r)) (Config.mk w ws n sa)))
  (exact (if-true-step w ws n d sa r hb))
  (constructor)
  (intro hx) (exact (And.left (ha e ht) (And.left (step-equiv _ _ e hs ht) hx)))
  (intro hx) (exact (And.right (step-equiv _ _ e hs ht) (And.right (ha e ht) hx))))

;; A step given by ev, then the rest of a reduction (chains of these make
;; certificates for straight-line arithmetic, cases/certified_horner.clj).
(a/theorem reach-ev [w :- World, ws :- Worlds, n :- Nat, t :- Tm, t2 :- Tm, m :- Config,
                     h :- (= Out (ev w ws n 0 t) (Out.next n t2)), hm :- (Star (Config.mk w ws n t2) m)]
  (Star (Config.mk w ws n t) m)
  (exact (Star.step _ _ _ (step-of-ev w ws n n t t2 h) hm)))
