(ns klara.formal.acct-typing
  "Affine soundness of λ-acct (L4.check.affine, design/11-profiles.md).

  The judgment `Acct.HasTy G t A e` is simply typed (data, tokens,
  functions with a latent effect flag) plus two kinds of premise that make
  it affine:

  - linearity at binders: a variable of type tok occurs at most once in its
    scope on every path (`Acct.occ` counts occurrences, the larger branch of
    an `if`);
  - no capture (`Acct.Tf`, token-free): a function body, a handler clause,
    and every part of a term that is still in the context while another
    part may perform (the effect flag `e`) holds no token and mentions no
    token variable. This is clause 7 of L4.check.affine (a continuation is
    multi-shot, authority is not) and clause 4 (no token captured).

  The invariant on configurations (`Acct.Inv`): every token id occurs at
  most once in the term, every id that occurs is live, and live ids are
  below the next id. The theorems:

    Acct.preservation   a typed configuration with the invariant steps to one
    Acct.progress       ... is a value, steps, performs an unhandled effect,
                        raises, or is stuck only for want of resources or on
                        a non-numeric amount; never on reuse
    Acct.erasure        ... steps the same with the reuse check erased"
  (:require [ansatz.core :as a]
            [klara.formal.acct]
            [klara.formal.acct-props]))

;; ---------------------------------------------------------------------------
;; Types, occurrences, contexts

(a/inductive Acct.Ty []
  (dat)
  (tok)
  (arr [a Acct.Ty] [b Acct.Ty] [e Bool]))

(a/defn Acct.unr [A :- Acct.Ty] Bool
  (match A [tok false] [_ true]))

(a/defn Acct.mx [a :- Nat, b :- Nat] Nat
  (match (Nat.ble a b) [true b] [false a]))

;; Occurrences of variable i (on the path with the most, for if).
(a/defn Acct.occ [i :- Nat, t :- Acct.Tm] Nat
  (match t
    [(var j) (match (Nat.beq i j) [true 1] [false 0])]
    [(lit d) 0]
    [(lam b) (Acct.occ (+ i 1) b)]
    [(app f x) (+ (Acct.occ i f) (Acct.occ i x))]
    [(let_ e b) (+ (Acct.occ i e) (Acct.occ (+ i 1) b))]
    [(if_ c u e) (+ (Acct.occ i c) (Acct.mx (Acct.occ i u) (Acct.occ i e)))]
    [(tok k) 0]
    [(take x) (Acct.occ i x)]
    [(spend u x) (+ (Acct.occ i u) (Acct.occ i x))]
    [(join u v) (+ (Acct.occ i u) (Acct.occ i v))]
    [(put u) (Acct.occ i u)]
    [(raise x) (Acct.occ i x)]
    [(try_ b h) (+ (Acct.occ i b) (Acct.occ (+ i 1) h))]
    [(perform op x) (Acct.occ i x)]
    [(handle ops b r o) (+ (Acct.occ i b) (+ (Acct.occ (+ i 1) r) (Acct.occ (+ i 3) o)))]
    [(handling ops b r o) (+ (Acct.occ i b) (+ (Acct.occ (+ i 1) r) (Acct.occ (+ i 3) o)))]))

;; Occurrences of token id m (on the path with the most, for if).
(a/defn Acct.cnt [m :- Nat, t :- Acct.Tm] Nat
  (match t
    [(var j) 0]
    [(lit d) 0]
    [(lam b) (Acct.cnt m b)]
    [(app f x) (+ (Acct.cnt m f) (Acct.cnt m x))]
    [(let_ e b) (+ (Acct.cnt m e) (Acct.cnt m b))]
    [(if_ c u e) (+ (Acct.cnt m c) (Acct.mx (Acct.cnt m u) (Acct.cnt m e)))]
    [(tok k) (match (Nat.beq m k) [true 1] [false 0])]
    [(take x) (Acct.cnt m x)]
    [(spend u x) (+ (Acct.cnt m u) (Acct.cnt m x))]
    [(join u v) (+ (Acct.cnt m u) (Acct.cnt m v))]
    [(put u) (Acct.cnt m u)]
    [(raise x) (Acct.cnt m x)]
    [(try_ b h) (+ (Acct.cnt m b) (Acct.cnt m h))]
    [(perform op x) (Acct.cnt m x)]
    [(handle ops b r o) (+ (Acct.cnt m b) (+ (Acct.cnt m r) (Acct.cnt m o)))]
    [(handling ops b r o) (+ (Acct.cnt m b) (+ (Acct.cnt m r) (Acct.cnt m o)))]))

(a/defn Acct.ctx [G :- (List Acct.Ty), i :- Nat] (Option Acct.Ty)
  (match G
    [nil (Option.none Acct.Ty)]
    [(cons A R) (match i [zero (Option.some Acct.Ty A)] [(succ k) (Acct.ctx R k)])]))

;; G without its entry j (what substituting for variable j leaves).
(a/defn Acct.dl [G :- (List Acct.Ty), j :- Nat] (List Acct.Ty)
  (match G
    [nil (List.nil Acct.Ty)]
    [(cons A R) (match j [zero R] [(succ k) (List.cons Acct.Ty A (Acct.dl R k))])]))

;; Token-free under k binders: no token, and no token variable of G.
(a/inductive Acct.Tf [] :in Prop :indices [k Nat G (List Acct.Ty) t Acct.Tm]
  (mk [k Nat] [G (List Acct.Ty)] [t Acct.Tm]
      [hc (forall [m :- Nat] (= Nat (Acct.cnt m t) 0))]
      [ho (forall [i :- Nat] (=> (= (Option Acct.Ty) (Acct.ctx G i) (Option.some Acct.Ty Acct.Ty.tok))
                                 (= Nat (Acct.occ (+ i k) t) 0)))]
      :where [k G t]))

;; ---------------------------------------------------------------------------
;; The judgment

(a/inductive Acct.HasTy [] :in Prop :indices [G (List Acct.Ty) t Acct.Tm A Acct.Ty e Bool]
  (var [G (List Acct.Ty)] [i Nat] [A Acct.Ty] [h (= (Option Acct.Ty) (Acct.ctx G i) (Option.some Acct.Ty A))]
       :where [G (Acct.Tm.var i) A Bool.false])
  (lit [G (List Acct.Ty)] [d Acct.Datum] :where [G (Acct.Tm.lit d) Acct.Ty.dat Bool.false])
  (tok [G (List Acct.Ty)] [k Nat] :where [G (Acct.Tm.tok k) Acct.Ty.tok Bool.false])
  (lam [G (List Acct.Ty)] [A Acct.Ty] [B Acct.Ty] [e Bool] [b Acct.Tm]
       [hb (Acct.HasTy (List.cons Acct.Ty A G) b B e)]
       [hl (=> (= Bool (Acct.unr A) Bool.false) (LE.le Nat instLENat (Acct.occ 0 b) 1))]
       [hf (Acct.Tf 1 G b)]
       :where [G (Acct.Tm.lam b) (Acct.Ty.arr A B e) Bool.false])
  (app [G (List Acct.Ty)] [f Acct.Tm] [x Acct.Tm] [A Acct.Ty] [B Acct.Ty] [e1 Bool] [e2 Bool] [e3 Bool]
       [hf (Acct.HasTy G f (Acct.Ty.arr A B e3) e1)] [hx (Acct.HasTy G x A e2)]
       [hs (=> (= Bool e1 Bool.true) (Acct.Tf 0 G x))]
       :where [G (Acct.Tm.app f x) B (Bool.or e1 (Bool.or e2 e3))])
  (let_ [G (List Acct.Ty)] [e Acct.Tm] [b Acct.Tm] [A Acct.Ty] [B Acct.Ty] [e1 Bool] [e2 Bool]
        [he (Acct.HasTy G e A e1)] [hb (Acct.HasTy (List.cons Acct.Ty A G) b B e2)]
        [hl (=> (= Bool (Acct.unr A) Bool.false) (LE.le Nat instLENat (Acct.occ 0 b) 1))]
        [hs (=> (= Bool e1 Bool.true) (Acct.Tf 1 G b))]
        :where [G (Acct.Tm.let_ e b) B (Bool.or e1 e2)])
  (if_ [G (List Acct.Ty)] [c Acct.Tm] [u Acct.Tm] [e Acct.Tm] [A Acct.Ty] [e1 Bool] [e2 Bool] [e3 Bool]
       [hc (Acct.HasTy G c Acct.Ty.dat e1)] [hu (Acct.HasTy G u A e2)] [he (Acct.HasTy G e A e3)]
       [hs (=> (= Bool e1 Bool.true) (And (Acct.Tf 0 G u) (Acct.Tf 0 G e)))]
       :where [G (Acct.Tm.if_ c u e) A (Bool.or e1 (Bool.or e2 e3))])
  (take [G (List Acct.Ty)] [x Acct.Tm] [e1 Bool] [hx (Acct.HasTy G x Acct.Ty.dat e1)]
        :where [G (Acct.Tm.take x) Acct.Ty.tok e1])
  (spend [G (List Acct.Ty)] [u Acct.Tm] [x Acct.Tm] [e1 Bool]
         [hu (Acct.HasTy G u Acct.Ty.tok e1)] [hx (Acct.HasTy G x Acct.Ty.dat Bool.false)]
         [hs (=> (= Bool e1 Bool.true) (Acct.Tf 0 G x))]
         :where [G (Acct.Tm.spend u x) Acct.Ty.tok e1])
  (join [G (List Acct.Ty)] [u Acct.Tm] [v Acct.Tm] [e1 Bool]
        [hu (Acct.HasTy G u Acct.Ty.tok e1)] [hv (Acct.HasTy G v Acct.Ty.tok Bool.false)]
        [hs (=> (= Bool e1 Bool.true) (Acct.Tf 0 G v))]
        :where [G (Acct.Tm.join u v) Acct.Ty.tok e1])
  (put [G (List Acct.Ty)] [u Acct.Tm] [e1 Bool] [hu (Acct.HasTy G u Acct.Ty.tok e1)]
       :where [G (Acct.Tm.put u) Acct.Ty.dat e1])
  (raise [G (List Acct.Ty)] [x Acct.Tm] [A Acct.Ty] [e1 Bool] [hx (Acct.HasTy G x Acct.Ty.dat e1)]
         :where [G (Acct.Tm.raise x) A e1])
  (try_ [G (List Acct.Ty)] [b Acct.Tm] [h Acct.Tm] [A Acct.Ty] [e1 Bool] [e2 Bool]
        [hb (Acct.HasTy G b A e1)] [hh (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat G) h A e2)]
        [hs (=> (= Bool e1 Bool.true) (Acct.Tf 1 G h))]
        :where [G (Acct.Tm.try_ b h) A (Bool.or e1 e2)])
  (perform [G (List Acct.Ty)] [op Nat] [x Acct.Tm] [e1 Bool] [hx (Acct.HasTy G x Acct.Ty.dat e1)]
           :where [G (Acct.Tm.perform op x) Acct.Ty.dat Bool.true])
  (handle [G (List Acct.Ty)] [ops (List Nat)] [b Acct.Tm] [r Acct.Tm] [o Acct.Tm] [B Acct.Ty]
          [e1 Bool] [e2 Bool] [e3 Bool]
          [hb (Acct.HasTy G b Acct.Ty.dat e1)]
          [hr (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat G) r B e2)]
          [ho (Acct.HasTy (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                    (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat G))) o B e3)]
          [hfr (Acct.Tf 1 G r)] [hfo (Acct.Tf 3 G o)]
          :where [G (Acct.Tm.handle ops b r o) B Bool.true])
  (handling [G (List Acct.Ty)] [ops (List Nat)] [b Acct.Tm] [r Acct.Tm] [o Acct.Tm] [B Acct.Ty]
            [e1 Bool] [e2 Bool] [e3 Bool]
            [hb (Acct.HasTy G b Acct.Ty.dat e1)]
            [hr (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat G) r B e2)]
            [ho (Acct.HasTy (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                      (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat G))) o B e3)]
            [hfr (Acct.Tf 1 G r)] [hfo (Acct.Tf 3 G o)]
            :where [G (Acct.Tm.handling ops b r o) B Bool.true]))

;; ---------------------------------------------------------------------------
;; Contexts

(a/theorem Acct.ctx-dl-lt [G :- (List Acct.Ty)]
  (forall [j :- Nat] (forall [i :- Nat]
    (=> (< i j) (= (Option Acct.Ty) (Acct.ctx (Acct.dl G j) i) (Acct.ctx G i)))))
  (induction G)
  (all_goals (intro j) (intro i) (intro h))
  (all_goals (cases j))
  (all_goals (try (omega)))
  (all_goals (cases i))
  (all_goals (simp only [Acct.dl, Acct.ctx]))
  (all_goals (try (rfl)))
  (simp [Acct.ctx])
  (apply ih_tail) (omega))

(a/theorem Acct.ctx-dl-ge [G :- (List Acct.Ty)]
  (forall [j :- Nat] (forall [i :- Nat]
    (=> (<= j i) (= (Option Acct.Ty) (Acct.ctx (Acct.dl G j) i) (Acct.ctx G (+ i 1))))))
  (induction G)
  (all_goals (intro j) (intro i) (intro h))
  (all_goals (cases j))
  (all_goals (cases i))
  (all_goals (simp only [Acct.dl, Acct.ctx]))
  (all_goals (try (rfl)))
  (all_goals (try (omega)))
  (simp [Acct.ctx])
  (apply ih_tail) (omega))

(a/theorem Acct.ctx-some-lt [G :- (List Acct.Ty)]
  (forall [i :- Nat] (forall [A :- Acct.Ty]
    (=> (= (Option Acct.Ty) (Acct.ctx G i) (Option.some Acct.Ty A)) (< i (List.length Acct.Ty G)))))
  (induction G)
  (all_goals (intro i) (intro A) (intro h))
  (all_goals (cases i))
  (all_goals (simp only [Acct.ctx] at h))
  (all_goals (try (cases h)))
  (all_goals (simp [List.length]))
  (all_goals (try (omega)))
  (have hh (< n (List.length Acct.Ty tail))) (exact (ih_tail n A h))
  (omega))

(a/theorem Acct.scope [G :- (List Acct.Ty), t :- Acct.Tm, A :- Acct.Ty, e :- Bool, h :- (Acct.HasTy G t A e)]
  (forall [i :- Nat] (=> (<= (List.length Acct.Ty G) i) (= Nat (Acct.occ i t) 0)))
  (induction h)
  (all_goals (intro n) (intro hn))
  (all_goals (simp only [Acct.occ]))
  (all_goals (simp_all [Acct.mx, List.length]))
  (all_goals (try (and_then (apply ih_ho') (omega))))
  (have hl (< i (List.length Acct.Ty G))) (exact (Acct.ctx-some-lt G i A h))
  (have hne (Not (= Nat n i))) (omega)
  (rw [(Acct.beq-ne _ _ hne)]))

(a/theorem Acct.ctx-app-lt [G :- (List Acct.Ty)]
  (forall [H :- (List Acct.Ty)] (forall [i :- Nat]
    (=> (< i (List.length Acct.Ty G)) (= (Option Acct.Ty) (Acct.ctx (List.append Acct.Ty G H) i) (Acct.ctx G i)))))
  (induction G)
  (all_goals (intro H) (intro i) (intro h))
  (all_goals (simp [List.length] at h))
  (all_goals (try (omega)))
  (cases i)
  (all_goals (simp only [List.append, Acct.ctx]))
  (all_goals (try (rfl)))
  (apply ih_tail) (omega))

(a/theorem Acct.tf-weaken [k :- Nat, G :- (List Acct.Ty), t :- Acct.Tm, H :- (List Acct.Ty), h :- (Acct.Tf k G t),
                       hsc :- (forall [i :- Nat] (=> (<= (+ (List.length Acct.Ty G) k) i) (= Nat (Acct.occ i t) 0)))]
  (Acct.Tf k (List.append Acct.Ty G H) t)
  (cases h)
  (apply Acct.Tf.mk) (assumption)
  (intro i) (intro hi)
  (cases hl (Nat.blt i (List.length Acct.Ty G)))
  (have hge (<= (List.length Acct.Ty G) i)) (simp_all [Nat.blt_eq]) (omega)
  (apply hsc) (omega)
  (have hlt (< i (List.length Acct.Ty G))) (simp_all [Nat.blt_eq])
  (rw [(Acct.ctx-app-lt G H i hlt)] at hi)
  (exact (ho i hi)))

(a/theorem Acct.tf-weaken-ty [k :- Nat, G :- (List Acct.Ty), t :- Acct.Tm, H :- (List Acct.Ty), G2 :- (List Acct.Ty),
                          B :- Acct.Ty, e :- Bool, h :- (Acct.Tf k G t), ht :- (Acct.HasTy G2 t B e),
                          hl :- (= Nat (List.length Acct.Ty G2) (+ (List.length Acct.Ty G) k))]
  (Acct.Tf k (List.append Acct.Ty G H) t)
  (apply (Acct.tf-weaken k G t H h))
  (intro i) (intro hi)
  (have hl2 (<= (List.length Acct.Ty G2) i)) (omega)
  (exact (Acct.scope G2 t B e ht i hl2)))

(a/theorem Acct.weaken [G :- (List Acct.Ty), t :- Acct.Tm, A :- Acct.Ty, e :- Bool, h :- (Acct.HasTy G t A e)]
  (forall [H :- (List Acct.Ty)] (Acct.HasTy (List.append Acct.Ty G H) t A e))
  (induction h)
  (all_goals (intro H))
  (all_goals (constructor))
  (all_goals (try (first (exact (ih_hb H)) (exact (ih_hf H)) (exact (ih_hx H)) (exact (ih_he H)) (exact (ih_hc H))
                         (exact (ih_hu H)) (exact (ih_hv H)) (exact (ih_hh H)) (exact (ih_hr H)) (exact (ih_ho H)))))
  (all_goals (try (assumption)))
  (rw [(Acct.ctx-app-lt G H i (Acct.ctx-some-lt G i A h))]) (exact h)
  (exact (Acct.tf-weaken-ty 1 G b H (List.cons Acct.Ty A G) B e hf hb (Eq.refl _)))
  (intro q) (exact (Acct.tf-weaken-ty 0 G x H G A e2 (hs q) hx (Eq.refl _)))
  (intro q) (exact (Acct.tf-weaken-ty 1 G b H (List.cons Acct.Ty A G) B e2 (hs q) hb (Eq.refl _)))
  (intro q) (apply And.intro)
  (exact (Acct.tf-weaken-ty 0 G u H G A e2 (And.left (hs q)) hu (Eq.refl _)))
  (exact (Acct.tf-weaken-ty 0 G e H G A e3 (And.right (hs q)) he (Eq.refl _)))
  (intro q) (exact (Acct.tf-weaken-ty 0 G x H G Acct.Ty.dat Bool.false (hs q) hx (Eq.refl _)))
  (intro q) (exact (Acct.tf-weaken-ty 0 G v H G Acct.Ty.tok Bool.false (hs q) hv (Eq.refl _)))
  (intro q) (exact (Acct.tf-weaken-ty 1 G h H (List.cons Acct.Ty Acct.Ty.dat G) A e2 (hs q) hh (Eq.refl _)))
  (exact (Acct.tf-weaken-ty 1 G r H (List.cons Acct.Ty Acct.Ty.dat G) B e2 hfr hr (Eq.refl _)))
  (exact (Acct.tf-weaken-ty 3 G o H (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                      (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat G))) B e3 hfo ho (Eq.refl _)))
  (exact (Acct.tf-weaken-ty 1 G r H (List.cons Acct.Ty Acct.Ty.dat G) B e2 hfr hr (Eq.refl _)))
  (exact (Acct.tf-weaken-ty 3 G o H (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                      (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat G))) B e3 hfo ho (Eq.refl _))))

(a/theorem Acct.mx-l [a :- Nat, b :- Nat] (<= a (Acct.mx a b))
  (simp only [Acct.mx]) (cases h (Nat.ble a b)) (all_goals (simp_all [Nat.ble_eq])) (all_goals (try (omega))))

(a/theorem Acct.mx-r [a :- Nat, b :- Nat] (<= b (Acct.mx a b))
  (simp only [Acct.mx]) (cases h (Nat.ble a b)) (all_goals (simp_all [Nat.ble_eq])) (all_goals (try (omega))))

(a/theorem Acct.mx-le [a :- Nat, b :- Nat, c :- Nat, ha :- (<= a c), hb :- (<= b c)] (<= (Acct.mx a b) c)
  (simp only [Acct.mx]) (cases h (Nat.ble a b)) (all_goals (simp_all [Nat.ble_eq])))

(a/theorem Acct.mx-add-le [a :- Nat, b :- Nat, x :- Nat, y :- Nat]
  (<= (Acct.mx (+ a x) (+ b y)) (+ (Acct.mx a b) (Acct.mx x y)))
  (have h1 (<= a (Acct.mx a b))) (exact (Acct.mx-l a b))
  (have h2 (<= b (Acct.mx a b))) (exact (Acct.mx-r a b))
  (have h3 (<= x (Acct.mx x y))) (exact (Acct.mx-l x y))
  (have h4 (<= y (Acct.mx x y))) (exact (Acct.mx-r x y))
  (apply Acct.mx-le) (omega) (omega))

(a/theorem Acct.beq-t [a :- Nat, b :- Nat, h :- (= Bool (Nat.beq a b) Bool.true)] (= Nat a b) (grind))

(a/theorem Acct.blt-t [a :- Nat, b :- Nat, h :- (= Bool (Nat.blt a b) Bool.true)] (< a b) (grind))

(a/theorem Acct.blt-f [a :- Nat, b :- Nat, h :- (= Bool (Nat.blt a b) Bool.false)] (<= b a) (grind))

(a/theorem Acct.occ-var-ne [i :- Nat, k :- Nat, h :- (Not (= Nat i k))] (= Nat (Acct.occ i (Acct.Tm.var k)) 0)
  (simp only [Acct.occ]) (rw [(Acct.beq-ne i k h)]))

(a/theorem Acct.occ-var-eq [i :- Nat] (= Nat (Acct.occ i (Acct.Tm.var i)) 1)
  (simp [Acct.occ]))

(a/theorem Acct.occ-substVar-lt [v :- Acct.Tm, hv :- (forall [i :- Nat] (= Nat (Acct.occ i v) 0)), k :- Nat, j :- Nat, i :- Nat,
                               h :- (< i j)]
  (= Nat (Acct.occ i (Acct.substVar v k j)) (Acct.occ i (Acct.Tm.var k)))
  (simp only [Acct.substVar])
  (cases h1 (Nat.beq k j))
  (simp only [h1])
  (cases h2 (Nat.blt j k))
  (simp only [h2])
  (simp only [h2])
  (have hjk (< j k)) (exact (Acct.blt-t j k h2))
  (have n1 (Not (= Nat i (- k 1)))) (omega)
  (have n2 (Not (= Nat i k))) (omega)
  (rw [(Acct.occ-var-ne i (- k 1) n1), (Acct.occ-var-ne i k n2)])
  (simp only [h1])
  (have hkj (= Nat k j)) (exact (Acct.beq-t k j h1))
  (have n2 (Not (= Nat i k))) (omega)
  (rw [(hv i), (Acct.occ-var-ne i k n2)]))

(a/theorem Acct.occ-substVar-ge [v :- Acct.Tm, hv :- (forall [i :- Nat] (= Nat (Acct.occ i v) 0)), k :- Nat, j :- Nat, i :- Nat,
                               h :- (<= j i)]
  (= Nat (Acct.occ i (Acct.substVar v k j)) (Acct.occ (+ i 1) (Acct.Tm.var k)))
  (simp only [Acct.substVar])
  (cases h1 (Nat.beq k j))
  (simp only [h1])
  (cases h2 (Nat.blt j k))
  (simp only [h2])
  (have hkj (<= k j)) (exact (Acct.blt-f j k h2))
  (have hk (Not (= Nat k j))) (intro q) (rw [q] at h1) (simp at h1)
  (have n1 (Not (= Nat i k))) (omega)
  (have n2 (Not (= Nat (+ i 1) k))) (omega)
  (rw [(Acct.occ-var-ne i k n1), (Acct.occ-var-ne (+ i 1) k n2)])
  (simp only [h2])
  (have hjk (< j k)) (exact (Acct.blt-t j k h2))
  (cases hb (Nat.beq (+ i 1) k))
  (have hq (Not (= Nat (+ i 1) k))) (intro q) (rw [q] at hb) (simp at hb)
  (have n1 (Not (= Nat i (- k 1)))) (omega)
  (simp only [Acct.occ hb]) (rw [(Acct.beq-ne i (- k 1) n1)])
  (have hq (= Nat (+ i 1) k)) (exact (Acct.beq-t (+ i 1) k hb))
  (have hq2 (= Nat i (- k 1))) (omega)
  (simp only [Acct.occ hb]) (rw [(Eq.symm hq2)]) (simp)
  (simp only [h1])
  (have hkj (= Nat k j)) (exact (Acct.beq-t k j h1))
  (have n2 (Not (= Nat (+ i 1) k))) (omega)
  (rw [(hv i), (Acct.occ-var-ne (+ i 1) k n2)]))

(a/theorem Acct.occ-subst-lt [v :- Acct.Tm, hv :- (forall [i :- Nat] (= Nat (Acct.occ i v) 0)), t :- Acct.Tm]
  (forall [j :- Nat] (forall [n :- Nat] (=> (< n j) (= Nat (Acct.occ n (Acct.subst j v t)) (Acct.occ n t)))))
  (induction t)
  (all_goals (intro j) (intro n) (intro h))
  (simp only [Acct.subst]) (exact (Acct.occ-substVar-lt v hv i j n h))
  (all_goals (simp only [Acct.subst, Acct.occ]))
  (all_goals (try (simp_all [Acct.mx])))
  (all_goals (have q1 (< (+ n 1) (+ j 1))) (omega))
  (exact (ih_b (+ j 1) (+ n 1) q1))
  (exact (ih_b (+ j 1) (+ n 1) q1))
  (exact (ih_h (+ j 1) (+ n 1) q1))
  (all_goals (have q3 (< (+ n 3) (+ j 3))) (omega))
  (all_goals (have h1 (= Nat (Acct.occ (+ n 1) (Acct.subst (+ j 1) v r)) (Acct.occ (+ n 1) r))) (exact (ih_r (+ j 1) (+ n 1) q1)))
  (all_goals (have h2 (= Nat (Acct.occ (+ n 3) (Acct.subst (+ j 3) v o)) (Acct.occ (+ n 3) o))) (exact (ih_o (+ j 3) (+ n 3) q3)))
  (all_goals (omega)))

(a/theorem Acct.occ-subst-ge [v :- Acct.Tm, hv :- (forall [i :- Nat] (= Nat (Acct.occ i v) 0)), t :- Acct.Tm]
  (forall [j :- Nat] (forall [n :- Nat] (=> (<= j n) (= Nat (Acct.occ n (Acct.subst j v t)) (Acct.occ (+ n 1) t)))))
  (induction t)
  (all_goals (intro j) (intro n) (intro h))
  (simp only [Acct.subst]) (exact (Acct.occ-substVar-ge v hv i j n h))
  (all_goals (simp only [Acct.subst, Acct.occ]))
  (all_goals (try (simp_all [Acct.mx])))
  (all_goals (have q1 (<= (+ j 1) (+ n 1))) (omega))
  (all_goals (try (first (exact (ih_b (+ j 1) (+ n 1) q1)) (exact (ih_h (+ j 1) (+ n 1) q1)))))
  (all_goals (have q3 (<= (+ j 3) (+ n 3))) (omega))
  (all_goals (try (have h1 (= Nat (Acct.occ (+ n 1) (Acct.subst (+ j 1) v r)) (Acct.occ (+ (+ n 1) 1) r))) (exact (ih_r (+ j 1) (+ n 1) q1))))
  (all_goals (try (have h2 (= Nat (Acct.occ (+ n 3) (Acct.subst (+ j 3) v o)) (Acct.occ (+ (+ n 3) 1) o))) (exact (ih_o (+ j 3) (+ n 3) q3))))
  (all_goals (omega)))

(a/theorem Acct.mx-mono [a :- Nat, b :- Nat, c :- Nat, d :- Nat, h1 :- (<= a c), h2 :- (<= b d)]
  (<= (Acct.mx a b) (Acct.mx c d))
  (have x1 (<= c (Acct.mx c d))) (exact (Acct.mx-l c d))
  (have x2 (<= d (Acct.mx c d))) (exact (Acct.mx-r c d))
  (apply Acct.mx-le) (omega) (omega))

(a/theorem Acct.mx-zero [a :- Nat, b :- Nat, h :- (= Nat (Acct.mx a b) 0)] (And (= Nat a 0) (= Nat b 0))
  (have x1 (<= a (Acct.mx a b))) (exact (Acct.mx-l a b))
  (have x2 (<= b (Acct.mx a b))) (exact (Acct.mx-r a b))
  (apply And.intro) (omega) (omega))

(a/theorem Acct.cnt-subst-0 [m :- Nat, v :- Acct.Tm, hv :- (= Nat (Acct.cnt m v) 0), t :- Acct.Tm]
  (forall [j :- Nat] (= Nat (Acct.cnt m (Acct.subst j v t)) (Acct.cnt m t)))
  (induction t)
  (all_goals (intro j))
  (all_goals (simp only [Acct.subst, Acct.cnt]))
  (all_goals (try (simp_all [Acct.mx])))
  (simp only [Acct.substVar])
  (split) (simp only [Acct.cnt]) (exact hv)
  (cases q (Nat.blt j i)) (all_goals (simp [Acct.cnt])))

(a/theorem Acct.cnt-subst-nocc [m :- Nat, v :- Acct.Tm, t :- Acct.Tm]
  (forall [j :- Nat] (=> (= Nat (Acct.occ j t) 0) (= Nat (Acct.cnt m (Acct.subst j v t)) (Acct.cnt m t))))
  (induction t)
  (all_goals (intro j) (intro h))
  (all_goals (simp only [Acct.occ] at h))
  (all_goals (simp only [Acct.subst, Acct.cnt]))
  (all_goals (try (have hz (And (= Nat (Acct.occ j u) 0) (= Nat (Acct.occ j e) 0)))
                  (apply Acct.mx-zero) (omega)))
  (all_goals (try (simp_all [Acct.mx])))
  (simp only [Acct.substVar]) (cases q1 (Nat.beq j i))
  (have ne (Not (= Nat i j))) (intro qq) (rw [qq] at q1) (simp at q1)
  (rw [(Acct.beq-ne i j ne)])
  (cases q2 (Nat.blt j i)) (all_goals (simp [Acct.cnt]))
  (simp_all))

(a/theorem Acct.cnt-subst-tok [n :- Nat, t :- Acct.Tm]
  (forall [j :- Nat] (<= (Acct.cnt n (Acct.subst j (Acct.Tm.tok n) t)) (+ (Acct.cnt n t) (Acct.occ j t))))
  (induction t)
  (all_goals (intro j))
  (all_goals (simp only [Acct.subst, Acct.cnt, Acct.occ]))
  (case var
    (simp only [Acct.substVar])
    (cases q1 (Nat.beq i j))
    (cases q2 (Nat.blt j i)) (all_goals (simp [Acct.cnt]))
    (have e (= Nat i j)) (exact (Acct.beq-t i j q1))
    (rw [e]) (simp [Acct.cnt]))
  (case tok (cases q (Nat.beq n i)) (all_goals (simp_all)))
  (case lam (specialize ih_b (+ j 1)) (omega))
  (case app (specialize ih_f j) (specialize ih_x j) (omega))
  (case let_ (specialize ih_e j) (specialize ih_b (+ j 1)) (omega))
  (case if_ (specialize ih_c j) (specialize ih_u j) (specialize ih_e j)
    (have m1 (<= (Acct.mx (Acct.cnt n (Acct.subst j (Acct.Tm.tok n) u)) (Acct.cnt n (Acct.subst j (Acct.Tm.tok n) e)))
                 (Acct.mx (+ (Acct.cnt n u) (Acct.occ j u)) (+ (Acct.cnt n e) (Acct.occ j e)))))
    (exact (Acct.mx-mono _ _ _ _ ih_u ih_e))
    (have m2 (<= (Acct.mx (+ (Acct.cnt n u) (Acct.occ j u)) (+ (Acct.cnt n e) (Acct.occ j e)))
                 (+ (Acct.mx (Acct.cnt n u) (Acct.cnt n e)) (Acct.mx (Acct.occ j u) (Acct.occ j e)))))
    (exact (Acct.mx-add-le _ _ _ _))
    (omega))
  (case take (specialize ih_x j) (omega))
  (case spend (specialize ih_u j) (specialize ih_x j) (omega))
  (case join (specialize ih_u j) (specialize ih_v j) (omega))
  (case put (specialize ih_u j) (omega))
  (case raise (specialize ih_x j) (omega))
  (case try_ (specialize ih_b j) (specialize ih_h (+ j 1)) (omega))
  (case perform (specialize ih_x j) (omega))
  (case handle (specialize ih_b j) (specialize ih_r (+ j 1)) (specialize ih_o (+ j 3)) (omega))
  (case handling (specialize ih_b j) (specialize ih_r (+ j 1)) (specialize ih_o (+ j 3)) (omega))
  (case lit (omega)))

(a/theorem Acct.tf-subst [k :- Nat, G :- (List Acct.Ty), t :- Acct.Tm, j :- Nat, A :- Acct.Ty, v :- Acct.Tm,
                     h :- (Acct.Tf k G t), hA :- (= (Option Acct.Ty) (Acct.ctx G j) (Option.some Acct.Ty A)),
                     hv :- (forall [i :- Nat] (= Nat (Acct.occ i v) 0)),
                     hvu :- (=> (= Bool (Acct.unr A) Bool.true) (forall [m :- Nat] (= Nat (Acct.cnt m v) 0)))]
  (Acct.Tf k (Acct.dl G j) (Acct.subst (+ j k) v t))
  (cases h)
  (apply Acct.Tf.mk)
  (intro m)
  (cases A)
  (rw [(Acct.cnt-subst-0 m v (hvu (Eq.refl _) m) t (+ j k))]) (exact (hc m))
  (rw [(Acct.cnt-subst-nocc m v t (+ j k) (ho j hA))]) (exact (hc m))
  (rw [(Acct.cnt-subst-0 m v (hvu (Eq.refl _) m) t (+ j k))]) (exact (hc m))
  (intro i) (intro hi)
  (cases q (Nat.blt i j))
  (have ge (<= j i)) (exact (Acct.blt-f i j q))
  (rw [(Acct.ctx-dl-ge G j i ge)] at hi)
  (have ge2 (<= (+ j k) (+ i k))) (omega)
  (rw [(Acct.occ-subst-ge v hv t (+ j k) (+ i k) ge2)])
  (have e (= Nat (+ (+ i k) 1) (+ (+ i 1) k))) (omega)
  (rw [e]) (exact (ho (+ i 1) hi))
  (have lt (< i j)) (exact (Acct.blt-t i j q))
  (rw [(Acct.ctx-dl-lt G j i lt)] at hi)
  (have lt2 (< (+ i k) (+ j k))) (omega)
  (rw [(Acct.occ-subst-lt v hv t (+ j k) (+ i k) lt2)])
  (exact (ho i hi)))

(a/theorem Acct.tf-subst0 [G :- (List Acct.Ty), t :- Acct.Tm, j :- Nat, A :- Acct.Ty, v :- Acct.Tm,
                     h :- (Acct.Tf 0 G t), hA :- (= (Option Acct.Ty) (Acct.ctx G j) (Option.some Acct.Ty A)),
                     hv :- (forall [i :- Nat] (= Nat (Acct.occ i v) 0)),
                     hvu :- (=> (= Bool (Acct.unr A) Bool.true) (forall [m :- Nat] (= Nat (Acct.cnt m v) 0)))]
  (Acct.Tf 0 (Acct.dl G j) (Acct.subst j v t))
  (have hh (Acct.Tf 0 (Acct.dl G j) (Acct.subst (+ j 0) v t))) (exact (Acct.tf-subst 0 G t j A v h hA hv hvu))
  (simp only [Nat.add_zero] at hh) (exact hh))

(a/theorem Acct.le-occ-subst [b :- Acct.Tm, j :- Nat, v :- Acct.Tm, hv :- (forall [i :- Nat] (= Nat (Acct.occ i v) 0)),
                          h :- (<= (Acct.occ 0 b) 1)]
  (<= (Acct.occ 0 (Acct.subst (+ j 1) v b)) 1)
  (have z (< 0 (+ j 1))) (omega)
  (rw [(Acct.occ-subst-lt v hv b (+ j 1) 0 z)]) (exact h))

(a/theorem Acct.subst-ty [G :- (List Acct.Ty), t :- Acct.Tm, B :- Acct.Ty, e :- Bool, h :- (Acct.HasTy G t B e)]
  (forall [j :- Nat] (forall [A0 :- Acct.Ty] (forall [w0 :- Acct.Tm]
    (=> (= (Option Acct.Ty) (Acct.ctx G j) (Option.some Acct.Ty A0))
        (=> (Acct.HasTy (List.nil Acct.Ty) w0 A0 Bool.false)
            (=> (forall [i :- Nat] (= Nat (Acct.occ i w0) 0))
                (=> (=> (= Bool (Acct.unr A0) Bool.true) (forall [m :- Nat] (= Nat (Acct.cnt m w0) 0)))
                    (Acct.HasTy (Acct.dl G j) (Acct.subst j w0 t) B e))))))))
  (induction h)
  (all_goals (intro j) (intro A0) (intro w0) (intro hA) (intro hvt) (intro hvo) (intro hvc))
  (all_goals (simp only [Acct.subst]))
  (case var
    (simp only [Acct.substVar])
    (cases q1 (Nat.beq i j))
    (cases q2 (Nat.blt j i))
    (all_goals (simp only []))
    (have lt (< i j)) (have ne (Not (= Nat i j))) (intro qq) (rw [qq] at q1) (simp at q1)
    (have le (<= i j)) (exact (Acct.blt-f j i q2)) (omega)
    (apply Acct.HasTy.var) (rw [(Acct.ctx-dl-lt G j i lt)]) (exact h)
    (have lt (< j i)) (exact (Acct.blt-t j i q2))
    (have ge (<= j (- i 1))) (omega)
    (apply Acct.HasTy.var) (rw [(Acct.ctx-dl-ge G j (- i 1) ge)])
    (have e1 (= Nat (+ (- i 1) 1) i)) (omega)
    (rw [e1]) (exact h)
    (have eq (= Nat i j)) (exact (Acct.beq-t i j q1))
    (rw [eq] at h) (rw [h] at hA) (cases hA)
    (exact (Acct.weaken (List.nil Acct.Ty) w0 A Bool.false hvt (Acct.dl G j))))
  (case lit (constructor))
  (case tok (constructor))
  (case lam (apply Acct.HasTy.lam) (exact (ih_hb (+ j 1) A0 w0 hA hvt hvo hvc)) (intro q) (have z (< 0 (+ j 1))) (omega) (rw [(Acct.occ-subst-lt w0 hvo b (+ j 1) 0 z)]) (exact (hl q)) (exact (Acct.tf-subst 1 G b j A0 w0 hf hA hvo hvc)))
  (case app (exact (Acct.HasTy.app (Acct.dl G j) (Acct.subst j w0 f) (Acct.subst j w0 x) A B e1 e2 e3 (ih_hf j A0 w0 hA hvt hvo hvc) (ih_hx j A0 w0 hA hvt hvo hvc) (fn [q :- (= Bool e1 Bool.true)] (Acct.tf-subst0 G x j A0 w0 (hs q) hA hvo hvc)))))
  (case let_ (exact (Acct.HasTy.let_ (Acct.dl G j) (Acct.subst j w0 e) (Acct.subst (+ j 1) w0 b) A B e1 e2 (ih_he j A0 w0 hA hvt hvo hvc) (ih_hb (+ j 1) A0 w0 hA hvt hvo hvc) (fn [q :- (= Bool (Acct.unr A) Bool.false)] (Acct.le-occ-subst b j w0 hvo (hl q))) (fn [q :- (= Bool e1 Bool.true)] (Acct.tf-subst 1 G b j A0 w0 (hs q) hA hvo hvc)))))
  (case if_ (apply Acct.HasTy.if_) (exact (ih_hc j A0 w0 hA hvt hvo hvc)) (exact (ih_hu j A0 w0 hA hvt hvo hvc)) (exact (ih_he j A0 w0 hA hvt hvo hvc))
    (intro q) (apply And.intro) (exact (Acct.tf-subst0 G u j A0 w0 (And.left (hs q)) hA hvo hvc)) (exact (Acct.tf-subst0 G e j A0 w0 (And.right (hs q)) hA hvo hvc)))
  (case take (apply Acct.HasTy.take) (exact (ih_hx j A0 w0 hA hvt hvo hvc)))
  (case spend (apply Acct.HasTy.spend) (exact (ih_hu j A0 w0 hA hvt hvo hvc)) (exact (ih_hx j A0 w0 hA hvt hvo hvc)) (intro q) (exact (Acct.tf-subst0 G x j A0 w0 (hs q) hA hvo hvc)))
  (case join (apply Acct.HasTy.join) (exact (ih_hu j A0 w0 hA hvt hvo hvc)) (exact (ih_hv j A0 w0 hA hvt hvo hvc)) (intro q) (exact (Acct.tf-subst0 G v j A0 w0 (hs q) hA hvo hvc)))
  (case put (apply Acct.HasTy.put) (exact (ih_hu j A0 w0 hA hvt hvo hvc)))
  (case raise (apply Acct.HasTy.raise) (exact (ih_hx j A0 w0 hA hvt hvo hvc)))
  (case try_ (apply Acct.HasTy.try_) (exact (ih_hb j A0 w0 hA hvt hvo hvc)) (exact (ih_hh (+ j 1) A0 w0 hA hvt hvo hvc)) (intro q) (exact (Acct.tf-subst 1 G h j A0 w0 (hs q) hA hvo hvc)))
  (case perform (exact (Acct.HasTy.perform (Acct.dl G j) op (Acct.subst j w0 x) e1 (ih_hx j A0 w0 hA hvt hvo hvc))))
  (case handle (exact (Acct.HasTy.handle (Acct.dl G j) ops (Acct.subst j w0 b) (Acct.subst (+ j 1) w0 r) (Acct.subst (+ j 3) w0 o) B e1 e2 e3 (ih_hb j A0 w0 hA hvt hvo hvc) (ih_hr (+ j 1) A0 w0 hA hvt hvo hvc) (ih_ho (+ j 3) A0 w0 hA hvt hvo hvc) (Acct.tf-subst 1 G r j A0 w0 hfr hA hvo hvc) (Acct.tf-subst 3 G o j A0 w0 hfo hA hvo hvc))))
  (case handling (exact (Acct.HasTy.handling (Acct.dl G j) ops (Acct.subst j w0 b) (Acct.subst (+ j 1) w0 r) (Acct.subst (+ j 3) w0 o) B e1 e2 e3 (ih_hb j A0 w0 hA hvt hvo hvc) (ih_hr (+ j 1) A0 w0 hA hvt hvo hvc) (ih_ho (+ j 3) A0 w0 hA hvt hvo hvc) (Acct.tf-subst 1 G r j A0 w0 hfr hA hvo hvc) (Acct.tf-subst 3 G o j A0 w0 hfo hA hvo hvc)))))

(a/defn Acct.isVal [t :- Acct.Tm] Bool
  (match t [(lit d) true] [(lam b) true] [(tok i) true] [_ false]))

(a/theorem Acct.seq1-val [o :- Acct.Out, fr :- (=> Acct.Tm Acct.Tm), d :- Acct.Out,
                       h :- (= Acct.Out (Acct.seq1 o fr d) Acct.Out.val)] (= Acct.Out d Acct.Out.val)
  (cases o)
  (all_goals (simp [Acct.seq1, Acct.frame] at h))
  (all_goals (try (cases h)))
  (all_goals (try (exact h)))
  (all_goals (try (rfl))))

(a/theorem Acct.seq2-val [o1 :- Acct.Out, o2 :- Acct.Out, fr1 :- (=> Acct.Tm Acct.Tm), fr2 :- (=> Acct.Tm Acct.Tm),
                       d :- Acct.Out, h :- (= Acct.Out (Acct.seq2 o1 o2 fr1 fr2 d) Acct.Out.val)] (= Acct.Out d Acct.Out.val)
  (cases o1)
  (all_goals (simp [Acct.seq2, Acct.frame] at h))
  (all_goals (try (cases h)))
  (cases o2)
  (all_goals (simp [Acct.frame] at h))
  (all_goals (try (cases h)))
  (all_goals (try (exact h)))
  (all_goals (try (rfl))))

(a/theorem Acct.beta-nv [s :- Acct.Store, f :- Acct.Tm, x :- Acct.Tm] (Not (= Acct.Out (Acct.beta s f x) Acct.Out.val))
  (intro h) (cases f) (all_goals (simp [Acct.beta] at h)) (all_goals (cases h)))

(a/theorem Acct.spendH-nv [s :- Acct.Store, i :- Nat, n :- Nat, h :- (Option Nat)] (Not (= Acct.Out (Acct.spendH s i n h) Acct.Out.val))
  (intro q) (revert q) (cases h) (all_goals (simp only [Acct.spendH]))
  (all_goals (try (and_then (intro q) (cases q))))
  (cases s) (simp only []) (split) (all_goals (intro q) (cases q)))

(a/theorem Acct.takeStep-nv [s :- Acct.Store, x :- Acct.Tm] (Not (= Acct.Out (Acct.takeStep s x) Acct.Out.val))
  (intro h) (revert h) (simp only [Acct.takeStep])
  (split) (all_goals (try (and_then (intro h) (cases h))))
  (cases s) (simp only [Acct.takeN]) (split) (all_goals (intro h) (cases h)))

(a/theorem Acct.putStep-nv [c :- Bool, s :- Acct.Store, u :- Acct.Tm] (Not (= Acct.Out (Acct.putStep c s u) Acct.Out.val))
  (intro h) (revert h) (cases u) (all_goals (simp only [Acct.putStep]))
  (all_goals (try (and_then (intro h) (cases h))))
  (cases s) (simp only [Acct.putH])
  (split) (all_goals (intro h) (cases h)))

(a/theorem Acct.tryOut-nv [s :- Acct.Store, h :- Acct.Tm, o :- Acct.Out, b :- Acct.Tm] (Not (= Acct.Out (Acct.tryOut s h o b) Acct.Out.val))
  (intro q) (revert q) (cases o) (all_goals (simp only [Acct.tryOut])) (all_goals (intro q) (cases q)))

(a/theorem Acct.handlingOut-nv [s :- Acct.Store, ops :- (List Nat), r :- Acct.Tm, o :- Acct.Tm, ob :- Acct.Out, b :- Acct.Tm]
  (Not (= Acct.Out (Acct.handlingOut s ops r o ob b) Acct.Out.val))
  (intro q) (revert q) (cases ob) (all_goals (simp only [Acct.handlingOut]))
  (all_goals (try (and_then (intro q) (cases q))))
  (simp only [Acct.handleEff]) (split) (all_goals (intro q) (cases q)))

(a/theorem Acct.spendN-nv [c :- Bool, s :- Acct.Store, i :- Nat, x :- Acct.Tm] (Not (= Acct.Out (Acct.spendN c s i x) Acct.Out.val))
  (cases s)
  (unfold Acct.spendN)
  (cases qa (Acct.amount x))
  (all_goals (dsimp only))
  (intro h) (cases h)
  (intro h) (exact (Acct.spendH-nv _ _ _ _ h)))

(a/theorem Acct.spendStep-nv [c :- Bool, s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm] (Not (= Acct.Out (Acct.spendStep c s u x) Acct.Out.val))
  (cases u) (all_goals (unfold Acct.spendStep)) (all_goals (try (dsimp only)))
  (all_goals (first (exact (Acct.spendN-nv _ _ _ _)) (and_then (intro h) (cases h)))))

(a/theorem Acct.joinH-nv [s :- Acct.Store, i :- Nat, j :- Nat, h1 :- (Option Nat), h2 :- (Option Nat)]
  (Not (= Acct.Out (Acct.joinH s i j h1 h2) Acct.Out.val))
  (intro q) (revert q) (cases h1) (all_goals (cases h2)) (all_goals (cases s)) (all_goals (simp only [Acct.joinH]))
  (all_goals (intro q) (cases q)))

(a/theorem Acct.joinN-nv [c :- Bool, s :- Acct.Store, i :- Nat, j :- Nat] (Not (= Acct.Out (Acct.joinN c s i j) Acct.Out.val))
  (cases s) (unfold Acct.joinN)
  (cases qa (Bool.and c (Nat.beq i j)))
  (all_goals (dsimp only))
  (intro h) (exact (Acct.joinH-nv _ _ _ _ _ h))
  (intro h) (cases h))

(a/theorem Acct.joinStep-nv [c :- Bool, s :- Acct.Store, u :- Acct.Tm, v :- Acct.Tm] (Not (= Acct.Out (Acct.joinStep c s u v) Acct.Out.val))
  (cases u) (all_goals (cases v)) (all_goals (unfold Acct.joinStep)) (all_goals (try (dsimp only)))
  (all_goals (first (exact (Acct.joinN-nv _ _ _ _)) (and_then (intro h) (cases h)))))

(a/theorem Acct.ev-val [cf :- Bool, s :- Acct.Store, t :- Acct.Tm, hz :- (= Acct.Out (Acct.ev cf s t) Acct.Out.val)]
  (= Bool (Acct.isVal t) Bool.true)
  (cases t)
  (case var (simp only [Acct.ev] at hz) (try (cases hz)))
  (case lit (rfl))
  (case lam (rfl))
  (case app (exact (absurd (Acct.seq2-val (Acct.ev cf s f) (Acct.ev cf s x) (fn [f2 :- Acct.Tm] (Acct.Tm.app f2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.app f x2)) (Acct.beta s f x) hz) (Acct.beta-nv s f x))))
  (case let_ (have q (= Acct.Out (Acct.Out.next s (Acct.subst 0 e b)) Acct.Out.val))
    (exact (Acct.seq1-val (Acct.ev cf s e) (fn [e2 :- Acct.Tm] (Acct.Tm.let_ e2 b)) (Acct.Out.next s (Acct.subst 0 e b)) hz)) (cases q))
  (case if_ (have q (= Acct.Out (Acct.Out.next s (Acct.pick c u e)) Acct.Out.val))
    (exact (Acct.seq1-val (Acct.ev cf s c) (fn [q2 :- Acct.Tm] (Acct.Tm.if_ q2 u e)) (Acct.Out.next s (Acct.pick c u e)) hz)) (cases q))
  (case tok (rfl))
  (case take (exact (absurd (Acct.seq1-val (Acct.ev cf s x) (fn [x2 :- Acct.Tm] (Acct.Tm.take x2)) (Acct.takeStep s x) hz) (Acct.takeStep-nv s x))))
  (case spend (exact (absurd (Acct.seq2-val (Acct.ev cf s u) (Acct.ev cf s x) (fn [u2 :- Acct.Tm] (Acct.Tm.spend u2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.spend u x2)) (Acct.spendStep cf s u x) hz) (Acct.spendStep-nv cf s u x))))
  (case join (exact (absurd (Acct.seq2-val (Acct.ev cf s u) (Acct.ev cf s v) (fn [u2 :- Acct.Tm] (Acct.Tm.join u2 v)) (fn [v2 :- Acct.Tm] (Acct.Tm.join u v2)) (Acct.joinStep cf s u v) hz) (Acct.joinStep-nv cf s u v))))
  (case put (exact (absurd (Acct.seq1-val (Acct.ev cf s u) (fn [u2 :- Acct.Tm] (Acct.Tm.put u2)) (Acct.putStep cf s u) hz) (Acct.putStep-nv cf s u))))
  (case raise (have q (= Acct.Out (Acct.Out.exn x) Acct.Out.val))
    (exact (Acct.seq1-val (Acct.ev cf s x) (fn [x2 :- Acct.Tm] (Acct.Tm.raise x2)) (Acct.Out.exn x) hz)) (cases q))
  (case try_ (exact (absurd hz (Acct.tryOut-nv s h (Acct.ev cf s b) b))))
  (case perform (have q (= Acct.Out (Acct.Out.eff op x (Acct.Tm.var 0)) Acct.Out.val))
    (exact (Acct.seq1-val (Acct.ev cf s x) (fn [x2 :- Acct.Tm] (Acct.Tm.perform op x2)) (Acct.Out.eff op x (Acct.Tm.var 0)) hz)) (cases q))
  (case handle (simp only [Acct.ev] at hz) (try (cases hz)))
  (case handling (exact (absurd hz (Acct.handlingOut-nv s ops r o (Acct.ev cf s b) b)))))

(a/defn Acct.isLive [l :- Acct.Live, i :- Nat] Bool
  (match (Acct.find l i) [none false] [(some m) true]))

(a/defn Acct.lv [s :- Acct.Store] Acct.Live (match s [(mk w sp nx l) l]))

(a/defn Acct.nx [s :- Acct.Store] Nat (match s [(mk w sp nx l) nx]))

(a/inductive Acct.Inv [] :in Prop :indices [s Acct.Store t Acct.Tm]
  (mk [s Acct.Store] [t Acct.Tm]
      [h1 (forall [m :- Nat] (LE.le Nat instLENat (Acct.cnt m t) 1))]
      [h2 (forall [m :- Nat] (=> (= Nat (Acct.cnt m t) 1) (= Bool (Acct.isLive (Acct.lv s) m) Bool.true)))]
      [h3 (forall [m :- Nat] (=> (= Bool (Acct.isLive (Acct.lv s) m) Bool.true) (LT.lt Nat instLTNat m (Acct.nx s))))]
      :where [s t]))

(a/inductive Acct.StepRel [] :in Prop :indices [s Acct.Store t Acct.Tm s2 Acct.Store t2 Acct.Tm]
  (mk [s Acct.Store] [t Acct.Tm] [s2 Acct.Store] [t2 Acct.Tm]
      [ha (LE.le Nat instLENat (Acct.nx s) (Acct.nx s2))]
      [hb (forall [m :- Nat] (=> (LT.lt Nat instLTNat m (Acct.nx s))
            (=> (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true) (= Bool (Acct.isLive (Acct.lv s) m) Bool.true))))]
      [hb2 (forall [m :- Nat] (=> (LE.le Nat instLENat (Acct.nx s) m)
            (=> (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true) (LT.lt Nat instLTNat m (Acct.nx s2)))))]
      [hc (forall [m :- Nat] (=> (LT.lt Nat instLTNat m (Acct.nx s)) (LE.le Nat instLENat (Acct.cnt m t2) (Acct.cnt m t))))]
      [hd (forall [m :- Nat] (=> (LT.lt Nat instLTNat m (Acct.nx s))
            (=> (= Bool (Acct.isLive (Acct.lv s) m) Bool.true)
                (=> (= Bool (Acct.isLive (Acct.lv s2) m) Bool.false)
                    (And (= Nat (Acct.cnt m t2) 0) (LE.le Nat instLENat 1 (Acct.cnt m t)))))))]
      [he (forall [m :- Nat] (=> (LE.le Nat instLENat (Acct.nx s) m)
            (And (LE.le Nat instLENat (Acct.cnt m t2) 1)
                 (=> (= Nat (Acct.cnt m t2) 1) (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true)))))]
      :where [s t s2 t2]))

(a/theorem Acct.inv-step2 [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm,
                       hi :- (Acct.Inv s t), hr :- (Acct.StepRel s t s2 t2), m :- Nat,
                       c1 :- (= Nat (Acct.cnt m t2) 1)]
  (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true)
  (cases hi) (cases hr)
  (cases q (Nat.blt m (Acct.nx s)))
  (have g (<= (Acct.nx s) m)) (exact (Acct.blt-f _ _ q)) (exact (And.right (he m g) c1))
  (have l (< m (Acct.nx s))) (exact (Acct.blt-t _ _ q))
  (cases q2 (Acct.isLive (Acct.lv s2) m))
  (case true (rfl))
  (have x1 (<= (Acct.cnt m t2) (Acct.cnt m t))) (exact (hc m l))
  (have x2 (<= (Acct.cnt m t) 1)) (exact (h1 m))
  (have c0 (= Nat (Acct.cnt m t) 1)) (omega)
  (have z (And (= Nat (Acct.cnt m t2) 0) (LE.le Nat instLENat 1 (Acct.cnt m t)))) (exact (hd m l (h2 m c0) q2))
  (have z1 (= Nat (Acct.cnt m t2) 0)) (exact (And.left z))
  (exfalso) (omega))

(a/theorem Acct.inv-step1 [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm,
                       hi :- (Acct.Inv s t), hr :- (Acct.StepRel s t s2 t2), m :- Nat]
  (<= (Acct.cnt m t2) 1)
  (cases hi) (cases hr)
  (cases q (Nat.blt m (Acct.nx s)))
  (have g (<= (Acct.nx s) m)) (exact (Acct.blt-f _ _ q)) (exact (And.left (he m g)))
  (have l (< m (Acct.nx s))) (exact (Acct.blt-t _ _ q))
  (have x1 (<= (Acct.cnt m t2) (Acct.cnt m t))) (exact (hc m l))
  (have x2 (<= (Acct.cnt m t) 1)) (exact (h1 m))
  (omega))

(a/theorem Acct.inv-step3 [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm,
                       hi :- (Acct.Inv s t), hr :- (Acct.StepRel s t s2 t2), m :- Nat,
                       lv2 :- (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true)]
  (< m (Acct.nx s2))
  (cases hi) (cases hr)
  (cases q (Nat.blt m (Acct.nx s)))
  (have g (<= (Acct.nx s) m)) (exact (Acct.blt-f _ _ q)) (exact (hb2 m g lv2))
  (have l (< m (Acct.nx s))) (exact (Acct.blt-t _ _ q))
  (have l2 (< m (Acct.nx s))) (exact (h3 m (hb m l lv2)))
  (omega))

(a/theorem Acct.inv-step [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm,
                       hi :- (Acct.Inv s t), hr :- (Acct.StepRel s t s2 t2)]
  (Acct.Inv s2 t2)
  (exact (Acct.Inv.mk s2 t2 (Acct.inv-step1 s t s2 t2 hi hr) (Acct.inv-step2 s t s2 t2 hi hr) (Acct.inv-step3 s t s2 t2 hi hr))))

(a/theorem Acct.inv-1 [s :- Acct.Store, t :- Acct.Tm, hi :- (Acct.Inv s t), m :- Nat] (<= (Acct.cnt m t) 1)
  (cases hi) (exact (h1 m)))

(a/theorem Acct.inv-2 [s :- Acct.Store, t :- Acct.Tm, hi :- (Acct.Inv s t), m :- Nat, c :- (= Nat (Acct.cnt m t) 1)]
  (= Bool (Acct.isLive (Acct.lv s) m) Bool.true)
  (cases hi) (exact (h2 m c)))

(a/theorem Acct.inv-3 [s :- Acct.Store, t :- Acct.Tm, hi :- (Acct.Inv s t), m :- Nat,
                    c :- (= Bool (Acct.isLive (Acct.lv s) m) Bool.true)]
  (< m (Acct.nx s))
  (cases hi) (exact (h3 m c)))

(a/theorem Acct.frame-kf0 [s :- Acct.Store, e :- Acct.Tm, fr :- (=> Acct.Tm Acct.Tm), kf :- (=> Nat Nat),
                        hsum :- (forall [m :- Nat] (forall [x :- Acct.Tm] (= Nat (Acct.cnt m (fr x)) (+ (Acct.cnt m x) (kf m))))),
                        hi :- (Acct.Inv s (fr e)), m :- Nat, g :- (<= (Acct.nx s) m)]
  (= Nat (kf m) 0)
  (have u (<= (Acct.cnt m (fr e)) 1)) (exact (Acct.inv-1 _ _ hi m)) (rw [(hsum m e)] at u)
  (cases q (Nat.beq (kf m) 1))
  (have nz (Not (= Nat (kf m) 1))) (intro z) (rw [z] at q) (simp at q)
  (omega)
  (have k1 (= Nat (kf m) 1)) (exact (Acct.beq-t _ _ q))
  (have c1 (= Nat (Acct.cnt m (fr e)) 1)) (rw [(hsum m e)]) (omega)
  (have l (< m (Acct.nx s))) (exact (Acct.inv-3 _ _ hi m (Acct.inv-2 _ _ hi m c1)))
  (omega))

(a/theorem Acct.inv-sub [s :- Acct.Store, e :- Acct.Tm, fr :- (=> Acct.Tm Acct.Tm), kf :- (=> Nat Nat),
                        hsum :- (forall [m :- Nat] (forall [x :- Acct.Tm] (= Nat (Acct.cnt m (fr x)) (+ (Acct.cnt m x) (kf m))))),
                        hi :- (Acct.Inv s (fr e))]
  (Acct.Inv s e)
  (cases hi)
  (apply Acct.Inv.mk)
  (intro m) (have u (<= (Acct.cnt m (fr e)) 1)) (exact (h1 m)) (rw [(hsum m e)] at u) (omega)
  (intro m) (intro c1) (apply h2)
  (have u (<= (Acct.cnt m (fr e)) 1)) (exact (h1 m)) (rw [(hsum m e)] at u) (rw [(hsum m e)]) (omega)
  (exact h3))

(a/theorem Acct.rel-a [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm, hr :- (Acct.StepRel s t s2 t2)]
  (<= (Acct.nx s) (Acct.nx s2)) (cases hr) (exact ha))

(a/theorem Acct.rel-b [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm, hr :- (Acct.StepRel s t s2 t2), m :- Nat,
                    l :- (< m (Acct.nx s)), lv2 :- (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true)]
  (= Bool (Acct.isLive (Acct.lv s) m) Bool.true) (cases hr) (exact (hb m l lv2)))

(a/theorem Acct.rel-b2 [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm, hr :- (Acct.StepRel s t s2 t2), m :- Nat,
                    g :- (<= (Acct.nx s) m), lv2 :- (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true)]
  (< m (Acct.nx s2)) (cases hr) (exact (hb2 m g lv2)))

(a/theorem Acct.rel-c [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm, hr :- (Acct.StepRel s t s2 t2), m :- Nat,
                    l :- (< m (Acct.nx s))]
  (<= (Acct.cnt m t2) (Acct.cnt m t)) (cases hr) (exact (hc m l)))

(a/theorem Acct.rel-d [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm, hr :- (Acct.StepRel s t s2 t2), m :- Nat,
                    l :- (< m (Acct.nx s)), lv :- (= Bool (Acct.isLive (Acct.lv s) m) Bool.true),
                    lv2 :- (= Bool (Acct.isLive (Acct.lv s2) m) Bool.false)]
  (And (= Nat (Acct.cnt m t2) 0) (LE.le Nat instLENat 1 (Acct.cnt m t))) (cases hr) (exact (hd m l lv lv2)))

(a/theorem Acct.rel-e [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm, hr :- (Acct.StepRel s t s2 t2), m :- Nat,
                    g :- (<= (Acct.nx s) m)]
  (And (LE.le Nat instLENat (Acct.cnt m t2) 1) (=> (= Nat (Acct.cnt m t2) 1) (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true)))
  (cases hr) (exact (he m g)))

(a/theorem Acct.frame-rel [s :- Acct.Store, e :- Acct.Tm, s2 :- Acct.Store, e2 :- Acct.Tm,
                        fr :- (=> Acct.Tm Acct.Tm), kf :- (=> Nat Nat),
                        hsum :- (forall [m :- Nat] (forall [x :- Acct.Tm] (= Nat (Acct.cnt m (fr x)) (+ (Acct.cnt m x) (kf m))))),
                        hi :- (Acct.Inv s (fr e)), hr :- (Acct.StepRel s e s2 e2)]
  (Acct.StepRel s (fr e) s2 (fr e2))
  (apply Acct.StepRel.mk)
  (exact (Acct.rel-a _ _ _ _ hr)) (exact (Acct.rel-b _ _ _ _ hr)) (exact (Acct.rel-b2 _ _ _ _ hr))
  (intro m) (intro l) (rw [(hsum m e), (hsum m e2)])
  (have x (<= (Acct.cnt m e2) (Acct.cnt m e))) (exact (Acct.rel-c _ _ _ _ hr m l)) (omega)
  (intro m) (intro l) (intro lv) (intro lv2)
  (have z (And (= Nat (Acct.cnt m e2) 0) (LE.le Nat instLENat 1 (Acct.cnt m e)))) (exact (Acct.rel-d _ _ _ _ hr m l lv lv2))
  (have z1 (= Nat (Acct.cnt m e2) 0)) (exact (And.left z))
  (have z2 (<= 1 (Acct.cnt m e))) (exact (And.right z))
  (have u (<= (Acct.cnt m (fr e)) 1)) (exact (Acct.inv-1 _ _ hi m)) (rw [(hsum m e)] at u)
  (rw [(hsum m e), (hsum m e2)])
  (apply And.intro) (omega) (omega)
  (intro m) (intro g)
  (have k0 (= Nat (kf m) 0)) (exact (Acct.frame-kf0 s e fr kf hsum hi m g))
  (have z (And (LE.le Nat instLENat (Acct.cnt m e2) 1) (=> (= Nat (Acct.cnt m e2) 1) (= Bool (Acct.isLive (Acct.lv s2) m) Bool.true))))
  (exact (Acct.rel-e _ _ _ _ hr m g))
  (rw [(hsum m e2), k0])
  (apply And.intro)
  (have z1 (<= (Acct.cnt m e2) 1)) (exact (And.left z)) (omega)
  (intro c) (apply (And.right z)) (omega))

(a/inductive Acct.OK [] :in Prop :indices [s Acct.Store t Acct.Tm A Acct.Ty e Bool o Acct.Out]
  (val [s Acct.Store] [t Acct.Tm] [A Acct.Ty] [e Bool] :where [s t A e Acct.Out.val])
  (next [s Acct.Store] [t Acct.Tm] [A Acct.Ty] [e Bool] [s2 Acct.Store] [t2 Acct.Tm] [e2 Bool]
        [ht (Acct.HasTy (List.nil Acct.Ty) t2 A e2)]
        [he (=> (= Bool e2 Bool.true) (= Bool e Bool.true))]
        [hr (Acct.StepRel s t s2 t2)]
        :where [s t A e (Acct.Out.next s2 t2)])
  (eff [s Acct.Store] [t Acct.Tm] [A Acct.Ty] [e Bool] [op Nat] [v Acct.Tm] [k Acct.Tm] [ek Bool]
       [he (= Bool e Bool.true)]
       [hv (Acct.HasTy (List.nil Acct.Ty) v Acct.Ty.dat Bool.false)]
       [hvc (forall [m :- Nat] (= Nat (Acct.cnt m v) 0))]
       [hk (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k A ek)]
       [hkc (forall [m :- Nat] (= Nat (Acct.cnt m k) 0))]
       :where [s t A e (Acct.Out.eff op v k)])
  (exn [s Acct.Store] [t Acct.Tm] [A Acct.Ty] [e Bool] [v Acct.Tm]
       [hv (Acct.HasTy (List.nil Acct.Ty) v Acct.Ty.dat Bool.false)]
       [hvc (forall [m :- Nat] (= Nat (Acct.cnt m v) 0))]
       :where [s t A e (Acct.Out.exn v)])
  (stuck [s Acct.Store] [t Acct.Tm] [A Acct.Ty] [e Bool] [st Acct.Stuck]
         [h1 (Not (= Acct.Stuck st Acct.Stuck.reuse))] [h2 (Not (= Acct.Stuck st Acct.Stuck.scope))]
         :where [s t A e (Acct.Out.stuck st)]))

(a/theorem Acct.frame-ok [s :- Acct.Store, e :- Acct.Tm, A1 :- Acct.Ty, e1 :- Bool, o :- Acct.Out,
                       fr :- (=> Acct.Tm Acct.Tm), kf :- (=> Nat Nat), A :- Acct.Ty, ef :- Bool,
                       efn :- (=> Bool Bool), efk :- (=> Bool Bool),
                       hsum :- (forall [m :- Nat] (forall [x :- Acct.Tm] (= Nat (Acct.cnt m (fr x)) (+ (Acct.cnt m x) (kf m))))),
                       hi :- (Acct.Inv s (fr e)),
                       ho :- (Acct.OK s e A1 e1 o),
                       hn :- (forall [x :- Acct.Tm] (forall [f2 :- Bool]
                               (=> (Acct.HasTy (List.nil Acct.Ty) x A1 f2) (=> (=> (= Bool f2 Bool.true) (= Bool e1 Bool.true))
                                   (Acct.HasTy (List.nil Acct.Ty) (fr x) A (efn f2)))))),
                       hm :- (forall [f2 :- Bool] (=> (=> (= Bool f2 Bool.true) (= Bool e1 Bool.true))
                               (=> (= Bool (efn f2) Bool.true) (= Bool ef Bool.true)))),
                       hkf :- (=> (= Bool e1 Bool.true) (forall [k :- Acct.Tm] (forall [ek :- Bool]
                               (=> (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k A1 ek)
                                   (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) (fr k) A (efk ek)))))),
                       hz :- (=> (= Bool e1 Bool.true) (forall [m :- Nat] (= Nat (kf m) 0))),
                       hke :- (=> (= Bool e1 Bool.true) (= Bool ef Bool.true))]
  (Acct.OK s (fr e) A ef (Acct.frame o fr))
  (cases ho)
  (case val (simp only [Acct.frame]) (constructor))
  (case next (simp only [Acct.frame])
    (exact (Acct.OK.next _ _ _ _ _ _ _ (hn _ _ ht he) (hm _ he) (Acct.frame-rel _ _ _ _ fr kf hsum hi hr))))
  (case eff (simp only [Acct.frame])
    (apply Acct.OK.eff) (exact (hke he)) (assumption) (assumption)
    (exact (hkf he k ek hk))
    (intro m) (rw [(hsum m k), (hkc m), (hz he m)]))
  (case exn (simp only [Acct.frame]) (apply Acct.OK.exn) (assumption) (assumption))
  (case stuck (simp only [Acct.frame]) (apply Acct.OK.stuck) (assumption) (assumption)))

(a/theorem Acct.tf-c [k :- Nat, G :- (List Acct.Ty), t :- Acct.Tm, h :- (Acct.Tf k G t), m :- Nat] (= Nat (Acct.cnt m t) 0)
  (cases h) (exact (hc m)))

(a/theorem Acct.val-eff [G :- (List Acct.Ty), v :- Acct.Tm, A :- Acct.Ty, e :- Bool, h :- (Acct.HasTy G v A e),
                      hv :- (= Bool (Acct.isVal v) Bool.true)]
  (= Bool e Bool.false)
  (cases h)
  (all_goals (try (rfl)))
  (all_goals (simp [Acct.isVal] at hv)))

(a/theorem Acct.val-unr-cnt [v :- Acct.Tm, A :- Acct.Ty, e :- Bool, h :- (Acct.HasTy (List.nil Acct.Ty) v A e),
                          hv :- (= Bool (Acct.isVal v) Bool.true), hu :- (= Bool (Acct.unr A) Bool.true), m :- Nat]
  (= Nat (Acct.cnt m v) 0)
  (cases h)
  (all_goals (try (and_then (simp [Acct.isVal] at hv) (done))))
  (all_goals (try (and_then (simp [Acct.unr] at hu) (done))))
  (all_goals (simp only [Acct.cnt]))
  (exact (Acct.tf-c _ _ _ hf m)))

(a/defn Acct.tokId [t :- Acct.Tm] Nat (match t [(tok i) i] [_ 0]))

(a/theorem Acct.tok-of [v :- Acct.Tm, e :- Bool, h :- (Acct.HasTy (List.nil Acct.Ty) v Acct.Ty.tok e),
                     hv :- (= Bool (Acct.isVal v) Bool.true)]
  (= Acct.Tm v (Acct.Tm.tok (Acct.tokId v)))
  (cases v)
  (all_goals (try (and_then (simp [Acct.isVal] at hv) (done))))
  (all_goals (try (and_then (cases h) (done))))
  (simp [Acct.tokId]))

(a/theorem Acct.inv-zero [s :- Acct.Store, t :- Acct.Tm, hi :- (Acct.Inv s t), m :- Nat, g :- (<= (Acct.nx s) m)]
  (= Nat (Acct.cnt m t) 0)
  (have u (<= (Acct.cnt m t) 1)) (exact (Acct.inv-1 _ _ hi m))
  (cases q (Nat.beq (Acct.cnt m t) 1))
  (have nz (Not (= Nat (Acct.cnt m t) 1))) (intro z) (rw [z] at q) (simp at q)
  (omega)
  (have c1 (= Nat (Acct.cnt m t) 1)) (exact (Acct.beq-t _ _ q))
  (have l (< m (Acct.nx s))) (exact (Acct.inv-3 _ _ hi m (Acct.inv-2 _ _ hi m c1)))
  (omega))

(a/theorem Acct.pure-rel [s :- Acct.Store, t :- Acct.Tm, t2 :- Acct.Tm, hi :- (Acct.Inv s t),
                       hc :- (forall [m :- Nat] (<= (Acct.cnt m t2) (Acct.cnt m t)))]
  (Acct.StepRel s t s t2)
  (apply Acct.StepRel.mk)
  (omega)
  (intro m) (intro l) (intro lv) (exact lv)
  (intro m) (intro g) (intro lv) (have l (< m (Acct.nx s))) (exact (Acct.inv-3 _ _ hi m lv)) (omega)
  (intro m) (intro l) (exact (hc m))
  (intro m) (intro l) (intro lv) (intro lv2) (rw [lv] at lv2) (simp at lv2)
  (intro m) (intro g)
  (have z (= Nat (Acct.cnt m t) 0)) (exact (Acct.inv-zero _ _ hi m g))
  (have z2 (<= (Acct.cnt m t2) (Acct.cnt m t))) (exact (hc m))
  (apply And.intro) (omega) (intro c) (exfalso) (omega))

(a/theorem Acct.subst-cnt-le [x :- Acct.Tm, b :- Acct.Tm, A :- Acct.Ty, e :- Bool,
                           hx :- (Acct.HasTy (List.nil Acct.Ty) x A e), hv :- (= Bool (Acct.isVal x) Bool.true),
                           hl :- (=> (= Bool (Acct.unr A) Bool.false) (<= (Acct.occ 0 b) 1)), m :- Nat]
  (<= (Acct.cnt m (Acct.subst 0 x b)) (+ (Acct.cnt m b) (Acct.cnt m x)))
  (cases qu (Acct.unr A))
  (have l1 (<= (Acct.occ 0 b) 1)) (exact (hl qu))
  (cases A)
  (simp [Acct.unr] at qu)
  (have hx2 (= Acct.Tm x (Acct.Tm.tok (Acct.tokId x)))) (exact (Acct.tok-of x e hx hv))
  (rw [hx2])
  (cases qm (Nat.beq m (Acct.tokId x)))
  (have ne (Not (= Nat m (Acct.tokId x)))) (intro z) (rw [z] at qm) (simp at qm)
  (have c0 (= Nat (Acct.cnt m (Acct.Tm.tok (Acct.tokId x))) 0)) (simp only [Acct.cnt]) (rw [(Acct.beq-ne _ _ ne)])
  (rw [(Acct.cnt-subst-0 m _ c0 b 0)]) (omega)
  (have eq (= Nat m (Acct.tokId x))) (exact (Acct.beq-t _ _ qm))
  (rw [eq])
  (have t1 (<= (Acct.cnt (Acct.tokId x) (Acct.subst 0 (Acct.Tm.tok (Acct.tokId x)) b))
               (+ (Acct.cnt (Acct.tokId x) b) (Acct.occ 0 b)))) (exact (Acct.cnt-subst-tok (Acct.tokId x) b 0))
  (have c1 (= Nat (Acct.cnt (Acct.tokId x) (Acct.Tm.tok (Acct.tokId x))) 1)) (simp [Acct.cnt])
  (omega)
  (simp [Acct.unr] at qu)
  (have c0 (= Nat (Acct.cnt m x) 0)) (exact (Acct.val-unr-cnt x A e hx hv qu m))
  (rw [(Acct.cnt-subst-0 m x c0 b 0)]) (omega))

(a/theorem Acct.weaken1 [t :- Acct.Tm, A :- Acct.Ty, e :- Bool, h :- (Acct.HasTy (List.nil Acct.Ty) t A e)]
  (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) t A e)
  (exact (Acct.weaken (List.nil Acct.Ty) t A e h (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))))

(a/theorem Acct.tf-weaken1 [k :- Nat, t :- Acct.Tm, B :- Acct.Ty, e :- Bool, G2 :- (List Acct.Ty),
                         h :- (Acct.Tf k (List.nil Acct.Ty) t), ht :- (Acct.HasTy G2 t B e),
                         hl :- (= Nat (List.length Acct.Ty G2) k)]
  (Acct.Tf k (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) t)
  (have hl2 (= Nat (List.length Acct.Ty G2) (+ (List.length Acct.Ty (List.nil Acct.Ty)) k))) (simp [List.length]) (exact hl)
  (exact (Acct.tf-weaken-ty k (List.nil Acct.Ty) t (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) G2 B e h ht hl2)))

(a/theorem Acct.lam-inv-b [G :- (List Acct.Ty), b :- Acct.Tm, A :- Acct.Ty, B :- Acct.Ty, e3 :- Bool, e1 :- Bool,
                        h :- (Acct.HasTy G (Acct.Tm.lam b) (Acct.Ty.arr A B e3) e1)]
  (Acct.HasTy (List.cons Acct.Ty A G) b B e3)
  (cases h) (assumption))

(a/theorem Acct.lam-inv-l [G :- (List Acct.Ty), b :- Acct.Tm, A :- Acct.Ty, B :- Acct.Ty, e3 :- Bool, e1 :- Bool,
                        h :- (Acct.HasTy G (Acct.Tm.lam b) (Acct.Ty.arr A B e3) e1)]
  (=> (= Bool (Acct.unr A) Bool.false) (<= (Acct.occ 0 b) 1))
  (cases h) (assumption))

(a/theorem Acct.beta-ok [s :- Acct.Store, f :- Acct.Tm, x :- Acct.Tm, A :- Acct.Ty, B :- Acct.Ty, e1 :- Bool, e2 :- Bool, e3 :- Bool,
                      hf :- (Acct.HasTy (List.nil Acct.Ty) f (Acct.Ty.arr A B e3) e1),
                      hx :- (Acct.HasTy (List.nil Acct.Ty) x A e2), hi :- (Acct.Inv s (Acct.Tm.app f x)),
                      vf :- (= Bool (Acct.isVal f) Bool.true), vx :- (= Bool (Acct.isVal x) Bool.true)]
  (Acct.OK s (Acct.Tm.app f x) B (Bool.or e1 (Bool.or e2 e3)) (Acct.beta s f x))
  (have e20 (= Bool e2 Bool.false)) (exact (Acct.val-eff _ _ _ _ hx vx))
  (have hx0 (Acct.HasTy (List.nil Acct.Ty) x A Bool.false)) (rw [e20] at hx) (exact hx)
  (cases f)
  (all_goals (try (and_then (simp [Acct.isVal] at vf) (done))))
  (all_goals (try (and_then (simp only [Acct.beta]) (apply Acct.OK.stuck) (intro z) (cases z) (intro z) (cases z))))
  (simp only [Acct.beta])
  (have hb (Acct.HasTy (List.cons Acct.Ty A (List.nil Acct.Ty)) b B e3)) (exact (Acct.lam-inv-b _ _ _ _ _ _ hf))
  (have hl (=> (= Bool (Acct.unr A) Bool.false) (<= (Acct.occ 0 b) 1))) (exact (Acct.lam-inv-l _ _ _ _ _ _ hf))
  (have hvo (forall [i :- Nat] (= Nat (Acct.occ i x) 0)))
  (intro i) (apply (Acct.scope _ _ _ _ hx0)) (simp [List.length])
  (have hvc (=> (= Bool (Acct.unr A) Bool.true) (forall [m :- Nat] (= Nat (Acct.cnt m x) 0))))
  (intro q) (intro m) (exact (Acct.val-unr-cnt x A Bool.false hx0 vx q m))
  (apply (Acct.OK.next _ _ _ _ _ _ e3))
  (exact (Acct.subst-ty _ _ _ _ hb 0 A x (Eq.refl _) hx0 hvo hvc))
  (intro q) (rw [q]) (simp)
  (apply Acct.pure-rel) (exact hi)
  (intro m)
  (have u (<= (Acct.cnt m (Acct.subst 0 x b)) (+ (Acct.cnt m b) (Acct.cnt m x)))) (exact (Acct.subst-cnt-le x b A Bool.false hx0 vx hl m))
  (simp only [Acct.cnt]) (omega)
)

(a/theorem Acct.or-imp [a :- Bool, b :- Bool, c :- Bool, h :- (=> (= Bool a Bool.true) (= Bool b Bool.true)),
                     h2 :- (= Bool (Bool.or a c) Bool.true)] (= Bool (Bool.or b c) Bool.true)
  (cases a) (all_goals (cases b)) (all_goals (cases c)) (all_goals (simp_all)))

(a/theorem Acct.or-imp2 [a :- Bool, b :- Bool, c :- Bool, d :- Bool, h :- (=> (= Bool b Bool.true) (= Bool c Bool.true)),
                     h2 :- (= Bool (Bool.or a (Bool.or b d)) Bool.true)] (= Bool (Bool.or a (Bool.or c d)) Bool.true)
  (cases a) (all_goals (cases b)) (all_goals (cases c)) (all_goals (cases d)) (all_goals (simp_all)))

(a/theorem Acct.or-t1 [b :- Bool] (= Bool (Bool.or Bool.true b) Bool.true) (simp))

(a/theorem Acct.or-t2 [a :- Bool, c :- Bool] (= Bool (Bool.or a (Bool.or Bool.true c)) Bool.true) (cases a) (all_goals (simp)))

(a/theorem Acct.or-t3 [a :- Bool, b :- Bool] (= Bool (Bool.or a (Bool.or b Bool.true)) Bool.true) (cases a) (all_goals (cases b)) (all_goals (simp)))

(a/theorem Acct.or-l [a :- Bool, c :- Bool, h :- (= Bool a Bool.true)] (= Bool (Bool.or a c) Bool.true)
  (cases a) (all_goals (simp_all)))

(a/theorem Acct.or-m [a :- Bool, b :- Bool, c :- Bool, h :- (= Bool b Bool.true)] (= Bool (Bool.or a (Bool.or b c)) Bool.true)
  (cases a) (all_goals (cases b)) (all_goals (simp_all)))

(a/theorem Acct.or-r [a :- Bool, b :- Bool, c :- Bool, h :- (= Bool c Bool.true)] (= Bool (Bool.or a (Bool.or b c)) Bool.true)
  (cases a) (all_goals (cases b)) (all_goals (cases c)) (all_goals (simp_all)))

(a/theorem Acct.app-ok [s :- Acct.Store, f :- Acct.Tm, x :- Acct.Tm, A :- Acct.Ty, B :- Acct.Ty, e1 :- Bool, e2 :- Bool, e3 :- Bool,
                     hf :- (Acct.HasTy (List.nil Acct.Ty) f (Acct.Ty.arr A B e3) e1),
                     hx :- (Acct.HasTy (List.nil Acct.Ty) x A e2),
                     hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 0 (List.nil Acct.Ty) x)),
                     hi :- (Acct.Inv s (Acct.Tm.app f x)), o1 :- Acct.Out, o2 :- Acct.Out,
                     h1 :- (Acct.OK s f (Acct.Ty.arr A B e3) e1 o1),
                     h2 :- (=> (= Acct.Out o1 Acct.Out.val) (Acct.OK s x A e2 o2)),
                     hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal f) Bool.true)),
                     hv2 :- (=> (= Acct.Out o2 Acct.Out.val) (= Bool (Acct.isVal x) Bool.true))]
  (Acct.OK s (Acct.Tm.app f x) B (Bool.or e1 (Bool.or e2 e3))
           (Acct.seq2 o1 o2 (fn [f2 :- Acct.Tm] (Acct.Tm.app f2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.app f x2)) (Acct.beta s f x)))
  (have FR1 (Acct.OK s (Acct.Tm.app f x) B (Bool.or e1 (Bool.or e2 e3)) (Acct.frame o1 (fn [f2 :- Acct.Tm] (Acct.Tm.app f2 x)))))
  (apply (Acct.frame-ok s f (Acct.Ty.arr A B e3) e1 o1 (fn [f2 :- Acct.Tm] (Acct.Tm.app f2 x)) (fn [m :- Nat] (Acct.cnt m x)) B (Bool.or e1 (Bool.or e2 e3)) (fn [b :- Bool] (Bool.or b (Bool.or e2 e3))) (fn [b :- Bool] (Bool.or b (Bool.or e2 e3)))))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.app (List.nil Acct.Ty) y x A B f2 e2 e3 hy hx (fn [q :- (= Bool f2 Bool.true)] (hs (hf2 q)))))
  (intro f2) (intro hf2) (intro h) (exact (Acct.or-imp f2 e1 (Bool.or e2 e3) hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.app (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k x A B ek e2 e3 hk (Acct.weaken1 x A e2 hx) (fn [q :- (= Bool ek Bool.true)] (Acct.tf-weaken1 0 x A e2 (List.nil Acct.Ty) (hs he1) hx (Eq.refl _)))))
  (intro he1) (intro m) (exact (Acct.tf-c _ _ _ (hs he1) m))
  (intro he1) (exact (Acct.or-l _ _ he1))
  (cases o1)
  (case val
    (have vf (= Bool (Acct.isVal f) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have e10 (= Bool e1 Bool.false)) (exact (Acct.val-eff _ _ _ _ hf vf))
    (have ok2 (Acct.OK s x A e2 o2)) (exact (h2 (Eq.refl _)))
    (have hf0 (Acct.HasTy (List.nil Acct.Ty) f (Acct.Ty.arr A B e3) Bool.false)) (rw [e10] at hf) (exact hf)
    (have FR2 (Acct.OK s (Acct.Tm.app f x) B (Bool.or e1 (Bool.or e2 e3)) (Acct.frame o2 (fn [x2 :- Acct.Tm] (Acct.Tm.app f x2)))))
    (apply (Acct.frame-ok s x A e2 o2 (fn [x2 :- Acct.Tm] (Acct.Tm.app f x2)) (fn [m :- Nat] (Acct.cnt m f)) B (Bool.or e1 (Bool.or e2 e3)) (fn [b :- Bool] (Bool.or e1 (Bool.or b e3))) (fn [b :- Bool] (Bool.or e1 (Bool.or b e3)))))
    (intro m) (intro y) (simp only [Acct.cnt]) (omega)
    (exact hi)
    (exact ok2)
    (intro y) (intro f2) (intro hy) (intro hf2) (rw [e10]) (exact (Acct.HasTy.app (List.nil Acct.Ty) f y A B Bool.false f2 e3 hf0 hy (fn [q :- (= Bool Bool.false Bool.true)] (absurd q Bool.false_ne_true))))
    (intro f2) (intro hf2) (intro h) (exact (Acct.or-imp2 e1 f2 e2 e3 hf2 h))
    (intro he2) (intro k) (intro ek) (intro hk) (rw [e10]) (exact (Acct.HasTy.app (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) f k A B Bool.false ek e3 (Acct.weaken1 f _ Bool.false hf0) hk (fn [q :- (= Bool Bool.false Bool.true)] (absurd q Bool.false_ne_true))))
    (intro he2) (intro m) (exact (Acct.val-unr-cnt f (Acct.Ty.arr A B e3) Bool.false hf0 vf (Eq.refl _) m))
    (intro he2) (exact (Acct.or-m _ _ _ he2))
    (cases o2)
    (case val (simp only [Acct.seq2]) (exact (Acct.beta-ok s f x A B e1 e2 e3 hf hx hi vf (hv2 (Eq.refl _)))))
    (all_goals (exact FR2)))
  (all_goals (exact FR1))
  )

(a/theorem Acct.live-cons-eq [k :- Nat, a :- Nat, l :- Acct.Live] (= Bool (Acct.isLive (Acct.Live.cons k a l) k) Bool.true)
  (simp [Acct.isLive, Acct.find]))

(a/theorem Acct.live-cons-ne [k :- Nat, a :- Nat, l :- Acct.Live, m :- Nat, h :- (Not (= Nat k m))]
  (= Bool (Acct.isLive (Acct.Live.cons k a l) m) (Acct.isLive l m))
  (simp only [Acct.isLive, Acct.find]) (rw [(Acct.beq-ne k m h)]))

(a/theorem Acct.live-remove-ne [l :- Acct.Live, i :- Nat, m :- Nat, h :- (Not (= Nat i m))]
  (= Bool (Acct.isLive (Acct.remove l i) m) (Acct.isLive l m))
  (simp only [Acct.isLive]) (rw [(Acct.find-remove-ne l i m h)]))

(a/defn Acct.amt [l :- Acct.Live, i :- Nat] Nat (match (Acct.find l i) [none 0] [(some a) a]))

(a/theorem Acct.find-live [l :- Acct.Live, i :- Nat, h :- (= Bool (Acct.isLive l i) Bool.true)]
  (= (Option Nat) (Acct.find l i) (Option.some Nat (Acct.amt l i)))
  (revert h) (simp only [Acct.isLive, Acct.amt])
  (cases q (Acct.find l i))
  (all_goals (simp)))

(a/theorem Acct.remove-self [l :- Acct.Live]
  (forall [i :- Nat] (=> (= Bool (Acct.isLive (Acct.remove l i) i) Bool.true) (= Bool (Acct.isLive l i) Bool.true)))
  (induction l)
  (all_goals (intro i) (intro h))
  (simp [Acct.remove, Acct.isLive, Acct.find] at h)
  (cases q (Nat.beq id i))
  (have ne (Not (= Nat id i))) (intro z) (rw [z] at q) (simp at q)
  (have e1 (= Acct.Live (Acct.remove (Acct.Live.cons id amt rest) i) (Acct.Live.cons id amt (Acct.remove rest i))))
  (simp only [Acct.remove]) (rw [q])
  (rw [e1] at h) (rw [(Acct.live-cons-ne id amt (Acct.remove rest i) i ne)] at h)
  (rw [(Acct.live-cons-ne id amt rest i ne)]) (exact (ih_rest i h))
  (have eq (= Nat id i)) (exact (Acct.beq-t _ _ q)) (rw [eq]) (exact (Acct.live-cons-eq _ _ _)))

(a/theorem Acct.remove-sub [l :- Acct.Live, i :- Nat, m :- Nat, h :- (= Bool (Acct.isLive (Acct.remove l i) m) Bool.true)]
  (= Bool (Acct.isLive l m) Bool.true)
  (cases q (Nat.beq i m))
  (have ne (Not (= Nat i m))) (intro z) (rw [z] at q) (simp at q)
  (rw [(Acct.live-remove-ne l i m ne)] at h) (exact h)
  (have eq (= Nat i m)) (exact (Acct.beq-t _ _ q)) (rw [eq] at h) (exact (Acct.remove-self l m h)))

(a/theorem Acct.remove-gone [l :- Acct.Live, i :- Nat, m :- Nat, lv :- (= Bool (Acct.isLive l m) Bool.true),
                          lv2 :- (= Bool (Acct.isLive (Acct.remove l i) m) Bool.false)]
  (= Nat m i)
  (cases q (Nat.beq i m))
  (have ne (Not (= Nat i m))) (intro z) (rw [z] at q) (simp at q)
  (rw [(Acct.live-remove-ne l i m ne), lv] at lv2) (simp at lv2)
  (have eq (= Nat i m)) (exact (Acct.beq-t _ _ q)) (omega))

(a/theorem Acct.cnt-tok-ne [m :- Nat, k :- Nat, h :- (Not (= Nat m k))] (= Nat (Acct.cnt m (Acct.Tm.tok k)) 0)
  (simp only [Acct.cnt]) (rw [(Acct.beq-ne m k h)]))

(a/theorem Acct.cnt-tok-le [m :- Nat, k :- Nat] (<= (Acct.cnt m (Acct.Tm.tok k)) 1)
  (simp only [Acct.cnt]) (cases q (Nat.beq m k)) (all_goals (simp)))

(a/theorem Acct.new-tok-rel [w :- Nat, sp :- Nat, nx :- Nat, l :- Acct.Live, w2 :- Nat, sp2 :- Nat, l2 :- Acct.Live, a :- Nat,
                          t :- Acct.Tm, hi :- (Acct.Inv (Acct.Store.mk w sp nx l) t),
                          hsub :- (forall [m :- Nat] (=> (= Bool (Acct.isLive l2 m) Bool.true) (= Bool (Acct.isLive l m) Bool.true))),
                          hcons :- (forall [m :- Nat] (=> (= Bool (Acct.isLive l m) Bool.true) (=> (= Bool (Acct.isLive l2 m) Bool.false)
                                     (<= 1 (Acct.cnt m t)))))]
  (Acct.StepRel (Acct.Store.mk w sp nx l) t (Acct.Store.mk w2 sp2 (+ nx 1) (Acct.Live.cons nx a l2)) (Acct.Tm.tok nx))
  (apply Acct.StepRel.mk)
  (simp only [Acct.nx]) (omega)
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro l1) (intro lv2) (have ne (Not (= Nat nx m))) (omega) (rw [(Acct.live-cons-ne nx a l2 m ne)] at lv2) (exact (hsub m lv2))
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro g) (intro lv2) (cases q (Nat.beq nx m))
  (have ne (Not (= Nat nx m))) (intro z) (rw [z] at q) (simp at q)
  (rw [(Acct.live-cons-ne nx a l2 m ne)] at lv2)
  (have l3 (< m nx)) (exact (Acct.inv-3 _ _ hi m (hsub m lv2))) (omega)
  (have eq (= Nat nx m)) (exact (Acct.beq-t _ _ q)) (omega)
  (simp only [Acct.nx]) (intro m) (intro l1) (have ne (Not (= Nat m nx))) (omega) (rw [(Acct.cnt-tok-ne m nx ne)]) (omega)
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro l1) (intro lv) (intro lv2)
  (have ne (Not (= Nat m nx))) (omega) (have ne2 (Not (= Nat nx m))) (omega)
  (rw [(Acct.live-cons-ne nx a l2 m ne2)] at lv2)
  (apply And.intro) (exact (Acct.cnt-tok-ne m nx ne)) (exact (hcons m lv lv2))
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro g) (apply And.intro) (exact (Acct.cnt-tok-le m nx))
  (intro c) (cases q (Nat.beq m nx))
  (have ne (Not (= Nat m nx))) (intro z) (rw [z] at q) (simp at q) (rw [(Acct.cnt-tok-ne m nx ne)] at c) (simp at c)
  (have eq (= Nat m nx)) (exact (Acct.beq-t _ _ q)) (rw [eq]) (exact (Acct.live-cons-eq _ _ _))
  )

(a/theorem Acct.put-rel [w :- Nat, sp :- Nat, nx :- Nat, l :- Acct.Live, w2 :- Nat, l2 :- Acct.Live,
                      t :- Acct.Tm, hi :- (Acct.Inv (Acct.Store.mk w sp nx l) t),
                      hsub :- (forall [m :- Nat] (=> (= Bool (Acct.isLive l2 m) Bool.true) (= Bool (Acct.isLive l m) Bool.true))),
                      hcons :- (forall [m :- Nat] (=> (= Bool (Acct.isLive l m) Bool.true) (=> (= Bool (Acct.isLive l2 m) Bool.false)
                                 (<= 1 (Acct.cnt m t)))))]
  (Acct.StepRel (Acct.Store.mk w sp nx l) t (Acct.Store.mk w2 sp nx l2) (Acct.Tm.lit Acct.Datum.nil))
  (apply Acct.StepRel.mk)
  (simp only [Acct.nx]) (omega)
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro l1) (intro lv2) (exact (hsub m lv2))
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro g) (intro lv2)
  (have l3 (< m nx)) (exact (Acct.inv-3 _ _ hi m (hsub m lv2))) (omega)
  (simp only [Acct.nx]) (intro m) (intro l1) (try (simp only [Acct.cnt])) (try (omega))
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro l1) (intro lv) (intro lv2)
  (apply And.intro) (try (simp only [Acct.cnt])) (exact (hcons m lv lv2))
  (simp only [Acct.nx, Acct.lv]) (intro m) (intro g) (apply And.intro) (try (simp only [Acct.cnt])) (try (omega))
  (case he.right (intro hc) (simp [Acct.cnt] at hc))
  )

(a/theorem Acct.take-red [s :- Acct.Store, x :- Acct.Tm, e1 :- Bool, hi :- (Acct.Inv s (Acct.Tm.take x))]
  (Acct.OK s (Acct.Tm.take x) Acct.Ty.tok e1 (Acct.takeStep s x))
  (cases s)
  (unfold Acct.takeStep)
  (cases qa (Acct.amount x))
  (all_goals (try (dsimp only)))
  (apply Acct.OK.stuck) (intro z) (cases z) (intro z) (cases z)
  (unfold Acct.takeN) (try (dsimp only))
  (cases qb (Nat.ble val wallet))
  (all_goals (try (dsimp only)))
  (apply Acct.OK.stuck) (intro z) (cases z) (intro z) (cases z)
  (apply (Acct.OK.next _ _ _ _ _ _ Bool.false))
  (constructor)
  (intro q) (exact (absurd q Bool.false_ne_true))
  (apply Acct.new-tok-rel) (exact hi) (intro m) (intro h) (exact h) (intro m) (intro lv) (intro lv2) (rw [lv] at lv2) (simp at lv2)
  )

(a/theorem Acct.spend-red [s :- Acct.Store, i :- Nat, x :- Acct.Tm, e1 :- Bool, hi :- (Acct.Inv s (Acct.Tm.spend (Acct.Tm.tok i) x))]
  (Acct.OK s (Acct.Tm.spend (Acct.Tm.tok i) x) Acct.Ty.tok e1 (Acct.spendStep Bool.true s (Acct.Tm.tok i) x))
  (have u (<= (Acct.cnt i (Acct.Tm.spend (Acct.Tm.tok i) x)) 1)) (exact (Acct.inv-1 _ _ hi i))
  (have v (<= 1 (Acct.cnt i (Acct.Tm.spend (Acct.Tm.tok i) x)))) (simp [Acct.cnt])
  (have c1 (= Nat (Acct.cnt i (Acct.Tm.spend (Acct.Tm.tok i) x)) 1)) (omega)
  (have lvi (= Bool (Acct.isLive (Acct.lv s) i) Bool.true)) (exact (Acct.inv-2 _ _ hi i c1))
  (cases s)
  (have fi (= (Option Nat) (Acct.find live i) (Option.some Nat (Acct.amt live i)))) (exact (Acct.find-live live i lvi))
  (unfold Acct.spendStep) (try (dsimp only))
  (unfold Acct.spendN)
  (cases qa (Acct.amount x))
  (all_goals (try (dsimp only)))
  (apply Acct.OK.stuck) (intro z) (cases z) (intro z) (cases z)
  (show (Acct.OK (Acct.Store.mk wallet spent next live) (Acct.Tm.spend (Acct.Tm.tok i) x) Acct.Ty.tok e1
                 (Acct.spendH (Acct.Store.mk wallet spent next live) i val (Acct.find live i))))
  (rw [fi])
  (unfold Acct.spendH) (try (dsimp only))
  (cases qb (Nat.ble val (Acct.amt live i)))
  (all_goals (try (dsimp only)))
  (apply Acct.OK.stuck) (intro z) (cases z) (intro z) (cases z)
  (apply (Acct.OK.next _ _ _ _ _ _ Bool.false))
  (constructor)
  (intro q) (exact (absurd q Bool.false_ne_true))
  (apply Acct.new-tok-rel) (exact hi)
  (intro m) (intro h) (exact (Acct.remove-sub live i m h))
  (intro m) (intro lv) (intro lv2) (have eq (= Nat m i)) (exact (Acct.remove-gone live i m lv lv2)) (rw [eq]) (omega)
  )

(a/theorem Acct.put-red [s :- Acct.Store, i :- Nat, e1 :- Bool, hi :- (Acct.Inv s (Acct.Tm.put (Acct.Tm.tok i)))]
  (Acct.OK s (Acct.Tm.put (Acct.Tm.tok i)) Acct.Ty.dat e1 (Acct.putStep Bool.true s (Acct.Tm.tok i)))
  (have c1 (= Nat (Acct.cnt i (Acct.Tm.put (Acct.Tm.tok i))) 1)) (simp [Acct.cnt])
  (have lvi (= Bool (Acct.isLive (Acct.lv s) i) Bool.true)) (exact (Acct.inv-2 _ _ hi i c1))
  (cases s)
  (have fi (= (Option Nat) (Acct.find live i) (Option.some Nat (Acct.amt live i)))) (exact (Acct.find-live live i lvi))
  (show (Acct.OK (Acct.Store.mk wallet spent next live) (Acct.Tm.put (Acct.Tm.tok i)) Acct.Ty.dat e1
                 (Acct.putH (Acct.Store.mk wallet spent next live) i (Acct.find live i))))
  (rw [fi])
  (unfold Acct.putH) (try (dsimp only))
  (apply (Acct.OK.next _ _ _ _ _ _ Bool.false))
  (constructor)
  (intro q) (exact (absurd q Bool.false_ne_true))
  (apply Acct.put-rel) (exact hi)
  (intro m) (intro h) (exact (Acct.remove-sub live i m h))
  (intro m) (intro lv) (intro lv2) (have eq (= Nat m i)) (exact (Acct.remove-gone live i m lv lv2)) (rw [eq]) (omega)
  )

(a/theorem Acct.join-red [s :- Acct.Store, i :- Nat, j :- Nat, e1 :- Bool, hi :- (Acct.Inv s (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j)))]
  (Acct.OK s (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j)) Acct.Ty.tok e1 (Acct.joinStep Bool.true s (Acct.Tm.tok i) (Acct.Tm.tok j)))
  (have ne (Not (= Nat i j)))
  (intro z) (have u (<= (Acct.cnt i (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j))) 1)) (exact (Acct.inv-1 _ _ hi i))
  (rw [z] at u) (simp [Acct.cnt] at u)
  (have ci (= Nat (Acct.cnt i (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j))) 1))
  (simp only [Acct.cnt]) (rw [(Acct.beq-ne i j ne)]) (simp)
  (have ne2 (Not (= Nat j i))) (omega)
  (have cj (= Nat (Acct.cnt j (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j))) 1))
  (simp only [Acct.cnt]) (rw [(Acct.beq-ne j i ne2)]) (simp)
  (have lvi (= Bool (Acct.isLive (Acct.lv s) i) Bool.true)) (exact (Acct.inv-2 _ _ hi i ci))
  (have lvj (= Bool (Acct.isLive (Acct.lv s) j) Bool.true)) (exact (Acct.inv-2 _ _ hi j cj))
  (cases s)
  (have fi (= (Option Nat) (Acct.find live i) (Option.some Nat (Acct.amt live i)))) (exact (Acct.find-live live i lvi))
  (have fj (= (Option Nat) (Acct.find live j) (Option.some Nat (Acct.amt live j)))) (exact (Acct.find-live live j lvj))
  (show (Acct.OK (Acct.Store.mk wallet spent next live) (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j)) Acct.Ty.tok e1
                 (Acct.joinN Bool.true (Acct.Store.mk wallet spent next live) i j)))
  (unfold Acct.joinN) (rw [(Acct.beq-ne i j ne)]) (try (dsimp only))
  (show (Acct.OK (Acct.Store.mk wallet spent next live) (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j)) Acct.Ty.tok e1
                 (Acct.joinH (Acct.Store.mk wallet spent next live) i j (Acct.find live i) (Acct.find live j))))
  (rw [fi, fj])
  (unfold Acct.joinH) (try (dsimp only))
  (apply (Acct.OK.next _ _ _ _ _ _ Bool.false))
  (constructor)
  (intro q) (exact (absurd q Bool.false_ne_true))
  (apply Acct.new-tok-rel) (exact hi)
  (intro m) (intro h) (exact (Acct.remove-sub live i m (Acct.remove-sub (Acct.remove live i) j m h)))
  (intro m) (intro lv) (intro lv2)
  (cases q (Acct.isLive (Acct.remove live i) m))
  (have eq (= Nat m i)) (exact (Acct.remove-gone live i m lv q)) (rw [eq, ci]) (omega)
  (have eq (= Nat m j)) (exact (Acct.remove-gone (Acct.remove live i) j m q lv2)) (rw [eq, cj]) (omega)
  )

(a/theorem Acct.inv-le [s :- Acct.Store, t :- Acct.Tm, e :- Acct.Tm, hi :- (Acct.Inv s t),
                     hle :- (forall [m :- Nat] (<= (Acct.cnt m e) (Acct.cnt m t)))]
  (Acct.Inv s e)
  (apply Acct.Inv.mk)
  (intro m) (have u (<= (Acct.cnt m t) 1)) (exact (Acct.inv-1 _ _ hi m)) (have v (<= (Acct.cnt m e) (Acct.cnt m t))) (exact (hle m)) (omega)
  (intro m) (intro c) (apply (Acct.inv-2 _ _ hi m))
  (have u (<= (Acct.cnt m t) 1)) (exact (Acct.inv-1 _ _ hi m)) (have v (<= (Acct.cnt m e) (Acct.cnt m t))) (exact (hle m)) (omega)
  (intro m) (intro c) (exact (Acct.inv-3 _ _ hi m c)))

(a/theorem Acct.or-r2 [a :- Bool, c :- Bool, h :- (= Bool c Bool.true)] (= Bool (Bool.or a c) Bool.true)
  (cases a) (all_goals (simp_all)))

(a/theorem Acct.ff-of [f :- Bool, h :- (=> (= Bool f Bool.true) (= Bool Bool.false Bool.true))] (= Bool f Bool.false)
  (cases f) (rfl) (exfalso) (exact (Bool.false_ne_true (h (Eq.refl _)))))

(a/theorem Acct.tt-ff [] (Not (= Bool Bool.true Bool.false)) (intro h) (cases h))

(a/theorem Acct.ok-exn-v [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, e :- Bool, v :- Acct.Tm, h :- (Acct.OK s t A e (Acct.Out.exn v))]
  (Acct.HasTy (List.nil Acct.Ty) v Acct.Ty.dat Bool.false) (cases h) (assumption))

(a/theorem Acct.ok-exn-c [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, e :- Bool, v :- Acct.Tm, h :- (Acct.OK s t A e (Acct.Out.exn v)), m :- Nat]
  (= Nat (Acct.cnt m v) 0) (cases h) (exact (hvc m)))

(a/theorem Acct.closed0 [v :- Acct.Tm, A :- Acct.Ty, e :- Bool, h :- (Acct.HasTy (List.nil Acct.Ty) v A e), i :- Nat]
  (= Nat (Acct.occ i v) 0)
  (apply (Acct.scope _ _ _ _ h)) (simp [List.length]))

(a/theorem Acct.let-ok [s :- Acct.Store, e :- Acct.Tm, b :- Acct.Tm, A :- Acct.Ty, B :- Acct.Ty, e1 :- Bool, e2 :- Bool,
                     he :- (Acct.HasTy (List.nil Acct.Ty) e A e1),
                     hb :- (Acct.HasTy (List.cons Acct.Ty A (List.nil Acct.Ty)) b B e2),
                     hl :- (=> (= Bool (Acct.unr A) Bool.false) (<= (Acct.occ 0 b) 1)),
                     hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 1 (List.nil Acct.Ty) b)),
                     hi :- (Acct.Inv s (Acct.Tm.let_ e b)), o1 :- Acct.Out,
                     h1 :- (Acct.OK s e A e1 o1),
                     hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal e) Bool.true))]
  (Acct.OK s (Acct.Tm.let_ e b) B (Bool.or e1 e2)
           (Acct.seq1 o1 (fn [y :- Acct.Tm] (Acct.Tm.let_ y b)) (Acct.Out.next s (Acct.subst 0 e b))))
  (have FR1 (Acct.OK s (Acct.Tm.let_ e b) B (Bool.or e1 e2) (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.let_ y b)))))
  (apply (Acct.frame-ok s e A e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.let_ y b)) (fn [m :- Nat] (Acct.cnt m b)) B (Bool.or e1 e2) (fn [f :- Bool] (Bool.or f e2)) (fn [f :- Bool] (Bool.or f e2))))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.let_ (List.nil Acct.Ty) y b A B f2 e2 hy hb hl (fn [q :- (= Bool f2 Bool.true)] (hs (hf2 q)))))
  (intro f2) (intro hf2) (intro h) (exact (Acct.or-imp f2 e1 e2 hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.let_ (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k b A B ek e2 hk (Acct.weaken (List.cons Acct.Ty A (List.nil Acct.Ty)) b B e2 hb (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty))) hl (fn [q :- (= Bool ek Bool.true)] (Acct.tf-weaken1 1 b B e2 (List.cons Acct.Ty A (List.nil Acct.Ty)) (hs he1) hb (Eq.refl _)))))
  (intro he1) (intro m) (exact (Acct.tf-c _ _ _ (hs he1) m))
  (intro he1) (exact (Acct.or-l _ _ he1))
  (cases o1)
  (case val
    (have ve (= Bool (Acct.isVal e) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have e10 (= Bool e1 Bool.false)) (exact (Acct.val-eff _ _ _ _ he ve))
    (have he0 (Acct.HasTy (List.nil Acct.Ty) e A Bool.false)) (rw [e10] at he) (exact he)
    (simp only [Acct.seq1])
    (apply (Acct.OK.next _ _ _ _ _ _ e2))
    (exact (Acct.subst-ty _ _ _ _ hb 0 A e (Eq.refl _) he0 (Acct.closed0 e A Bool.false he0) (fn [q :- (= Bool (Acct.unr A) Bool.true)] (Acct.val-unr-cnt e A Bool.false he0 ve q))))
    (intro q) (exact (Acct.or-r2 _ _ q))
    (apply Acct.pure-rel) (exact hi)
    (intro m)
    (have u (<= (Acct.cnt m (Acct.subst 0 e b)) (+ (Acct.cnt m b) (Acct.cnt m e)))) (exact (Acct.subst-cnt-le e b A Bool.false he0 ve hl m))
    (simp only [Acct.cnt]) (omega))
  (all_goals (exact FR1))
  )

(a/theorem Acct.if-ok [s :- Acct.Store, c :- Acct.Tm, u :- Acct.Tm, e :- Acct.Tm, A :- Acct.Ty, e1 :- Bool, e2 :- Bool, e3 :- Bool,
                    hc :- (Acct.HasTy (List.nil Acct.Ty) c Acct.Ty.dat e1),
                    hu :- (Acct.HasTy (List.nil Acct.Ty) u A e2), he :- (Acct.HasTy (List.nil Acct.Ty) e A e3),
                    hs :- (=> (= Bool e1 Bool.true) (And (Acct.Tf 0 (List.nil Acct.Ty) u) (Acct.Tf 0 (List.nil Acct.Ty) e))),
                    hi :- (Acct.Inv s (Acct.Tm.if_ c u e)), o1 :- Acct.Out,
                    h1 :- (Acct.OK s c Acct.Ty.dat e1 o1)]
  (Acct.OK s (Acct.Tm.if_ c u e) A (Bool.or e1 (Bool.or e2 e3))
           (Acct.seq1 o1 (fn [q :- Acct.Tm] (Acct.Tm.if_ q u e)) (Acct.Out.next s (Acct.pick c u e))))
  (have FR1 (Acct.OK s (Acct.Tm.if_ c u e) A (Bool.or e1 (Bool.or e2 e3)) (Acct.frame o1 (fn [q :- Acct.Tm] (Acct.Tm.if_ q u e)))))
  (apply (Acct.frame-ok s c Acct.Ty.dat e1 o1 (fn [q :- Acct.Tm] (Acct.Tm.if_ q u e)) (fn [m :- Nat] (Acct.mx (Acct.cnt m u) (Acct.cnt m e))) A (Bool.or e1 (Bool.or e2 e3)) (fn [f :- Bool] (Bool.or f (Bool.or e2 e3))) (fn [f :- Bool] (Bool.or f (Bool.or e2 e3)))))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.if_ (List.nil Acct.Ty) y u e A f2 e2 e3 hy hu he (fn [q :- (= Bool f2 Bool.true)] (hs (hf2 q)))))
  (intro f2) (intro hf2) (intro h) (exact (Acct.or-imp f2 e1 (Bool.or e2 e3) hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.if_ (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k u e A ek e2 e3 hk (Acct.weaken1 u A e2 hu) (Acct.weaken1 e A e3 he) (fn [q :- (= Bool ek Bool.true)] (And.intro (Acct.tf-weaken1 0 u A e2 (List.nil Acct.Ty) (And.left (hs he1)) hu (Eq.refl _)) (Acct.tf-weaken1 0 e A e3 (List.nil Acct.Ty) (And.right (hs he1)) he (Eq.refl _))))))
  (intro he1) (intro m)
  (have a1 (= Nat (Acct.cnt m u) 0)) (exact (Acct.tf-c _ _ _ (And.left (hs he1)) m))
  (have a2 (= Nat (Acct.cnt m e) 0)) (exact (Acct.tf-c _ _ _ (And.right (hs he1)) m))
  (show (= Nat (Acct.mx (Acct.cnt m u) (Acct.cnt m e)) 0)) (rw [a1, a2])
  (intro he1) (exact (Acct.or-l _ _ he1))
  (cases o1)
  (case val
    (show (Acct.OK s (Acct.Tm.if_ c u e) A (Bool.or e1 (Bool.or e2 e3)) (Acct.Out.next s (Acct.pick c u e))))
    (unfold Acct.pick)
    (cases qt (Acct.truthy c))
    (all_goals (try (dsimp only)))
    (apply (Acct.OK.next _ _ _ _ _ _ e3))
    (exact he)
    (intro q) (exact (Acct.or-r _ _ _ q))
    (apply Acct.pure-rel) (exact hi) (intro m)
    (show (<= (Acct.cnt m e) (+ (Acct.cnt m c) (Acct.mx (Acct.cnt m u) (Acct.cnt m e)))))
    (have x1 (<= (Acct.cnt m e) (Acct.mx (Acct.cnt m u) (Acct.cnt m e)))) (exact (Acct.mx-r _ _)) (omega)
    (apply (Acct.OK.next _ _ _ _ _ _ e2))
    (exact hu)
    (intro q) (exact (Acct.or-m _ _ _ q))
    (apply Acct.pure-rel) (exact hi) (intro m)
    (show (<= (Acct.cnt m u) (+ (Acct.cnt m c) (Acct.mx (Acct.cnt m u) (Acct.cnt m e)))))
    (have x1 (<= (Acct.cnt m u) (Acct.mx (Acct.cnt m u) (Acct.cnt m e)))) (exact (Acct.mx-l _ _)) (omega))
  (all_goals (exact FR1))
  )

(a/theorem Acct.take-ok [s :- Acct.Store, x :- Acct.Tm, e1 :- Bool,
                      hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat e1),
                      hi :- (Acct.Inv s (Acct.Tm.take x)), o1 :- Acct.Out, h1 :- (Acct.OK s x Acct.Ty.dat e1 o1)]
  (Acct.OK s (Acct.Tm.take x) Acct.Ty.tok e1 (Acct.seq1 o1 (fn [y :- Acct.Tm] (Acct.Tm.take y)) (Acct.takeStep s x)))
  (have FR1 (Acct.OK s (Acct.Tm.take x) Acct.Ty.tok e1 (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.take y)))))
  (apply (Acct.frame-ok s x Acct.Ty.dat e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.take y)) (fn [m :- Nat] 0) Acct.Ty.tok e1 (fn [f :- Bool] f) (fn [f :- Bool] f)))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.take (List.nil Acct.Ty) y f2 hy))
  (intro f2) (intro hf2) (intro h) (exact (hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.take (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k ek hk))
  (intro he1) (intro m) (rfl)
  (intro he1) (exact he1)
  (cases o1)
  (case val (exact (Acct.take-red s x e1 hi)))
  (all_goals (exact FR1)))

(a/theorem Acct.put-ok [s :- Acct.Store, u :- Acct.Tm, e1 :- Bool,
                     hu :- (Acct.HasTy (List.nil Acct.Ty) u Acct.Ty.tok e1),
                     hi :- (Acct.Inv s (Acct.Tm.put u)), o1 :- Acct.Out, h1 :- (Acct.OK s u Acct.Ty.tok e1 o1),
                     hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal u) Bool.true))]
  (Acct.OK s (Acct.Tm.put u) Acct.Ty.dat e1 (Acct.seq1 o1 (fn [y :- Acct.Tm] (Acct.Tm.put y)) (Acct.putStep Bool.true s u)))
  (have FR1 (Acct.OK s (Acct.Tm.put u) Acct.Ty.dat e1 (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.put y)))))
  (apply (Acct.frame-ok s u Acct.Ty.tok e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.put y)) (fn [m :- Nat] 0) Acct.Ty.dat e1 (fn [f :- Bool] f) (fn [f :- Bool] f)))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.put (List.nil Acct.Ty) y f2 hy))
  (intro f2) (intro hf2) (intro h) (exact (hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.put (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k ek hk))
  (intro he1) (intro m) (rfl)
  (intro he1) (exact he1)
  (cases o1)
  (case val
    (have vu (= Bool (Acct.isVal u) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have eu (= Acct.Tm u (Acct.Tm.tok (Acct.tokId u)))) (exact (Acct.tok-of u e1 hu vu))
    (rw [eu] at hi) (rw [eu])
    (exact (Acct.put-red s (Acct.tokId u) e1 hi)))
  (all_goals (exact FR1)))

(a/theorem Acct.raise-ok [s :- Acct.Store, x :- Acct.Tm, A :- Acct.Ty, e1 :- Bool,
                       hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat e1),
                       hi :- (Acct.Inv s (Acct.Tm.raise x)), o1 :- Acct.Out, h1 :- (Acct.OK s x Acct.Ty.dat e1 o1),
                       hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal x) Bool.true))]
  (Acct.OK s (Acct.Tm.raise x) A e1 (Acct.seq1 o1 (fn [y :- Acct.Tm] (Acct.Tm.raise y)) (Acct.Out.exn x)))
  (have FR1 (Acct.OK s (Acct.Tm.raise x) A e1 (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.raise y)))))
  (apply (Acct.frame-ok s x Acct.Ty.dat e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.raise y)) (fn [m :- Nat] 0) A e1 (fn [f :- Bool] f) (fn [f :- Bool] f)))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.raise (List.nil Acct.Ty) y A f2 hy))
  (intro f2) (intro hf2) (intro h) (exact (hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.raise (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k A ek hk))
  (intro he1) (intro m) (rfl)
  (intro he1) (exact he1)
  (cases o1)
  (case val
    (have vx (= Bool (Acct.isVal x) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have e10 (= Bool e1 Bool.false)) (exact (Acct.val-eff _ _ _ _ hx vx))
    (have hx0 (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat Bool.false)) (rw [e10] at hx) (exact hx)
    (exact (Acct.OK.exn s (Acct.Tm.raise x) A e1 x hx0 (Acct.val-unr-cnt x Acct.Ty.dat Bool.false hx0 vx (Eq.refl _)))))
  (all_goals (exact FR1)))

(a/theorem Acct.perform-ok [s :- Acct.Store, op :- Nat, x :- Acct.Tm, e1 :- Bool,
                         hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat e1),
                         hi :- (Acct.Inv s (Acct.Tm.perform op x)), o1 :- Acct.Out, h1 :- (Acct.OK s x Acct.Ty.dat e1 o1),
                         hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal x) Bool.true))]
  (Acct.OK s (Acct.Tm.perform op x) Acct.Ty.dat Bool.true
           (Acct.seq1 o1 (fn [y :- Acct.Tm] (Acct.Tm.perform op y)) (Acct.Out.eff op x (Acct.Tm.var 0))))
  (have FR1 (Acct.OK s (Acct.Tm.perform op x) Acct.Ty.dat Bool.true (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.perform op y)))))
  (apply (Acct.frame-ok s x Acct.Ty.dat e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.perform op y)) (fn [m :- Nat] 0) Acct.Ty.dat Bool.true (fn [f :- Bool] Bool.true) (fn [f :- Bool] Bool.true)))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.perform (List.nil Acct.Ty) op y f2 hy))
  (intro f2) (intro hf2) (intro h) (rfl)
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.perform (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) op k ek hk))
  (intro he1) (intro m) (rfl)
  (intro he1) (rfl)
  (cases o1)
  (case val
    (have vx (= Bool (Acct.isVal x) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have e10 (= Bool e1 Bool.false)) (exact (Acct.val-eff _ _ _ _ hx vx))
    (have hx0 (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat Bool.false)) (rw [e10] at hx) (exact hx)
    (exact (Acct.OK.eff s (Acct.Tm.perform op x) Acct.Ty.dat Bool.true op x (Acct.Tm.var 0) Bool.false (Eq.refl _) hx0
             (Acct.val-unr-cnt x Acct.Ty.dat Bool.false hx0 vx (Eq.refl _))
             (Acct.HasTy.var (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) 0 Acct.Ty.dat (Eq.refl _))
             (fn [m :- Nat] (Eq.refl _)))))
  (all_goals (exact FR1)))

(a/theorem Acct.ff-eq [e1 :- Bool, u :- Acct.Tm, A :- Acct.Ty, hu :- (Acct.HasTy (List.nil Acct.Ty) u A e1),
                    vu :- (= Bool (Acct.isVal u) Bool.true)]
  (Not (= Bool e1 Bool.true))
  (have e0 (= Bool e1 Bool.false)) (exact (Acct.val-eff _ _ _ _ hu vu))
  (rw [e0]) (exact Bool.false_ne_true))

(a/theorem Acct.spend-ok [s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm, e1 :- Bool,
                       hu :- (Acct.HasTy (List.nil Acct.Ty) u Acct.Ty.tok e1),
                       hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat Bool.false),
                       hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 0 (List.nil Acct.Ty) x)),
                       hi :- (Acct.Inv s (Acct.Tm.spend u x)), o1 :- Acct.Out, o2 :- Acct.Out,
                       h1 :- (Acct.OK s u Acct.Ty.tok e1 o1),
                       h2 :- (=> (= Acct.Out o1 Acct.Out.val) (Acct.OK s x Acct.Ty.dat Bool.false o2)),
                       hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal u) Bool.true))]
  (Acct.OK s (Acct.Tm.spend u x) Acct.Ty.tok e1
           (Acct.seq2 o1 o2 (fn [y :- Acct.Tm] (Acct.Tm.spend y x)) (fn [y :- Acct.Tm] (Acct.Tm.spend u y)) (Acct.spendStep Bool.true s u x)))
  (have FR1 (Acct.OK s (Acct.Tm.spend u x) Acct.Ty.tok e1 (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.spend y x)))))
  (apply (Acct.frame-ok s u Acct.Ty.tok e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.spend y x)) (fn [m :- Nat] (Acct.cnt m x)) Acct.Ty.tok e1 (fn [f :- Bool] f) (fn [f :- Bool] f)))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.spend (List.nil Acct.Ty) y x f2 hy hx (fn [q :- (= Bool f2 Bool.true)] (hs (hf2 q)))))
  (intro f2) (intro hf2) (intro h) (exact (hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.spend (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k x ek hk (Acct.weaken1 x Acct.Ty.dat Bool.false hx) (fn [q :- (= Bool ek Bool.true)] (Acct.tf-weaken1 0 x Acct.Ty.dat Bool.false (List.nil Acct.Ty) (hs he1) hx (Eq.refl _)))))
  (intro he1) (intro m) (exact (Acct.tf-c _ _ _ (hs he1) m))
  (intro he1) (exact he1)
  (cases o1)
  (case val
    (have vu (= Bool (Acct.isVal u) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have ok2 (Acct.OK s x Acct.Ty.dat Bool.false o2)) (exact (h2 (Eq.refl _)))
    (have FR2 (Acct.OK s (Acct.Tm.spend u x) Acct.Ty.tok e1 (Acct.frame o2 (fn [y :- Acct.Tm] (Acct.Tm.spend u y)))))
    (apply (Acct.frame-ok s x Acct.Ty.dat Bool.false o2 (fn [y :- Acct.Tm] (Acct.Tm.spend u y)) (fn [m :- Nat] (Acct.cnt m u)) Acct.Ty.tok e1 (fn [f :- Bool] e1) (fn [f :- Bool] e1)))
    (intro m) (intro y) (simp only [Acct.cnt]) (omega)
    (exact hi)
    (exact ok2)
    (intro y) (intro f2) (intro hy) (intro hf2)
    (have f20 (= Bool f2 Bool.false)) (exact (Acct.ff-of f2 hf2))
    (rw [f20] at hy)
    (exact (Acct.HasTy.spend (List.nil Acct.Ty) u y e1 hu hy (fn [q :- (= Bool e1 Bool.true)] (absurd q (Acct.ff-eq e1 u Acct.Ty.tok hu vu)))))
    (intro f2) (intro hf2) (intro h) (exact h)
    (intro q) (exact (absurd q Bool.false_ne_true))
    (intro q) (exact (absurd q Bool.false_ne_true))
    (intro q) (exact (absurd q Bool.false_ne_true))
    (cases o2)
    (case val
      (have eu (= Acct.Tm u (Acct.Tm.tok (Acct.tokId u)))) (exact (Acct.tok-of u e1 hu vu))
      (rw [eu] at hi) (rw [eu])
      (exact (Acct.spend-red s (Acct.tokId u) x e1 hi)))
    (all_goals (exact FR2)))
  (all_goals (exact FR1)))

(a/theorem Acct.join-ok [s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm, e1 :- Bool,
                       hu :- (Acct.HasTy (List.nil Acct.Ty) u Acct.Ty.tok e1),
                       hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.tok Bool.false),
                       hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 0 (List.nil Acct.Ty) x)),
                       hi :- (Acct.Inv s (Acct.Tm.join u x)), o1 :- Acct.Out, o2 :- Acct.Out,
                       h1 :- (Acct.OK s u Acct.Ty.tok e1 o1),
                       h2 :- (=> (= Acct.Out o1 Acct.Out.val) (Acct.OK s x Acct.Ty.tok Bool.false o2)),
                       hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal u) Bool.true)),
                       hv2 :- (=> (= Acct.Out o2 Acct.Out.val) (= Bool (Acct.isVal x) Bool.true))]
  (Acct.OK s (Acct.Tm.join u x) Acct.Ty.tok e1
           (Acct.seq2 o1 o2 (fn [y :- Acct.Tm] (Acct.Tm.join y x)) (fn [y :- Acct.Tm] (Acct.Tm.join u y)) (Acct.joinStep Bool.true s u x)))
  (have FR1 (Acct.OK s (Acct.Tm.join u x) Acct.Ty.tok e1 (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.join y x)))))
  (apply (Acct.frame-ok s u Acct.Ty.tok e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.join y x)) (fn [m :- Nat] (Acct.cnt m x)) Acct.Ty.tok e1 (fn [f :- Bool] f) (fn [f :- Bool] f)))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.join (List.nil Acct.Ty) y x f2 hy hx (fn [q :- (= Bool f2 Bool.true)] (hs (hf2 q)))))
  (intro f2) (intro hf2) (intro h) (exact (hf2 h))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.join (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k x ek hk (Acct.weaken1 x Acct.Ty.tok Bool.false hx) (fn [q :- (= Bool ek Bool.true)] (Acct.tf-weaken1 0 x Acct.Ty.tok Bool.false (List.nil Acct.Ty) (hs he1) hx (Eq.refl _)))))
  (intro he1) (intro m) (exact (Acct.tf-c _ _ _ (hs he1) m))
  (intro he1) (exact he1)
  (cases o1)
  (case val
    (have vu (= Bool (Acct.isVal u) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have ok2 (Acct.OK s x Acct.Ty.tok Bool.false o2)) (exact (h2 (Eq.refl _)))
    (have FR2 (Acct.OK s (Acct.Tm.join u x) Acct.Ty.tok e1 (Acct.frame o2 (fn [y :- Acct.Tm] (Acct.Tm.join u y)))))
    (apply (Acct.frame-ok s x Acct.Ty.tok Bool.false o2 (fn [y :- Acct.Tm] (Acct.Tm.join u y)) (fn [m :- Nat] (Acct.cnt m u)) Acct.Ty.tok e1 (fn [f :- Bool] e1) (fn [f :- Bool] e1)))
    (intro m) (intro y) (simp only [Acct.cnt]) (omega)
    (exact hi)
    (exact ok2)
    (intro y) (intro f2) (intro hy) (intro hf2)
    (have f20 (= Bool f2 Bool.false)) (exact (Acct.ff-of f2 hf2))
    (rw [f20] at hy)
    (exact (Acct.HasTy.join (List.nil Acct.Ty) u y e1 hu hy (fn [q :- (= Bool e1 Bool.true)] (absurd q (Acct.ff-eq e1 u Acct.Ty.tok hu vu)))))
    (intro f2) (intro hf2) (intro h) (exact h)
    (intro q) (exact (absurd q Bool.false_ne_true))
    (intro q) (exact (absurd q Bool.false_ne_true))
    (intro q) (exact (absurd q Bool.false_ne_true))
    (cases o2)
    (case val
      (have vx (= Bool (Acct.isVal x) Bool.true)) (exact (hv2 (Eq.refl _)))
      (have eu (= Acct.Tm u (Acct.Tm.tok (Acct.tokId u)))) (exact (Acct.tok-of u e1 hu vu))
      (have ex (= Acct.Tm x (Acct.Tm.tok (Acct.tokId x)))) (exact (Acct.tok-of x Bool.false hx vx))
      (rw [eu, ex] at hi) (rw [eu, ex])
      (exact (Acct.join-red s (Acct.tokId u) (Acct.tokId x) e1 hi)))
    (all_goals (exact FR2)))
  (all_goals (exact FR1)))

(a/theorem Acct.tf-nil [k :- Nat, t :- Acct.Tm, hc :- (forall [m :- Nat] (= Nat (Acct.cnt m t) 0))] (Acct.Tf k (List.nil Acct.Ty) t)
  (apply Acct.Tf.mk) (exact hc) (intro i) (intro q) (simp only [Acct.ctx] at q) (cases q))

(a/theorem Acct.handle-ok [s :- Acct.Store, ops :- (List Nat), b :- Acct.Tm, r :- Acct.Tm, o :- Acct.Tm, B :- Acct.Ty,
                        e1 :- Bool, e2 :- Bool, e3 :- Bool,
                        hb :- (Acct.HasTy (List.nil Acct.Ty) b Acct.Ty.dat e1),
                        hr :- (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) r B e2),
                        ho :- (Acct.HasTy (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                    (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) o B e3),
                        hfr :- (Acct.Tf 1 (List.nil Acct.Ty) r), hfo :- (Acct.Tf 3 (List.nil Acct.Ty) o),
                        hi :- (Acct.Inv s (Acct.Tm.handle ops b r o))]
  (Acct.OK s (Acct.Tm.handle ops b r o) B Bool.true (Acct.Out.next s (Acct.Tm.handling ops b r o)))
  (apply (Acct.OK.next _ _ _ _ _ _ Bool.true))
  (exact (Acct.HasTy.handling (List.nil Acct.Ty) ops b r o B e1 e2 e3 hb hr ho hfr hfo))
  (intro q) (rfl)
  (apply Acct.pure-rel) (exact hi) (intro m) (exact (Nat.le_refl _)))

(a/theorem Acct.try-ok [s :- Acct.Store, b :- Acct.Tm, h :- Acct.Tm, A :- Acct.Ty, e1 :- Bool, e2 :- Bool,
                     hb :- (Acct.HasTy (List.nil Acct.Ty) b A e1),
                     hh :- (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) h A e2),
                     hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 1 (List.nil Acct.Ty) h)),
                     hi :- (Acct.Inv s (Acct.Tm.try_ b h)), o1 :- Acct.Out, h1 :- (Acct.OK s b A e1 o1)]
  (Acct.OK s (Acct.Tm.try_ b h) A (Bool.or e1 e2) (Acct.tryOut s h o1 b))
  (have FR (Acct.OK s (Acct.Tm.try_ b h) A (Bool.or e1 e2) (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.try_ y h)))))
  (apply (Acct.frame-ok s b A e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.try_ y h)) (fn [m :- Nat] (Acct.cnt m h)) A (Bool.or e1 e2) (fn [f :- Bool] (Bool.or f e2)) (fn [f :- Bool] (Bool.or f e2))))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.try_ (List.nil Acct.Ty) y h A f2 e2 hy hh (fn [q :- (= Bool f2 Bool.true)] (hs (hf2 q)))))
  (intro f2) (intro hf2) (intro q) (exact (Acct.or-imp f2 e1 e2 hf2 q))
  (intro he1) (intro k) (intro ek) (intro hk) (exact (Acct.HasTy.try_ (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k h A ek e2 hk (Acct.weaken (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) h A e2 hh (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty))) (fn [q :- (= Bool ek Bool.true)] (Acct.tf-weaken1 1 h A e2 (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) (hs he1) hh (Eq.refl _)))))
  (intro he1) (intro m) (exact (Acct.tf-c _ _ _ (hs he1) m))
  (intro he1) (exact (Acct.or-l _ _ he1))
  (cases o1)
  (case val
    (show (Acct.OK s (Acct.Tm.try_ b h) A (Bool.or e1 e2) (Acct.Out.next s b)))
    (apply (Acct.OK.next _ _ _ _ _ _ e1))
    (exact hb)
    (intro q) (exact (Acct.or-l _ _ q))
    (apply Acct.pure-rel) (exact hi) (intro m) (show (<= (Acct.cnt m b) (+ (Acct.cnt m b) (Acct.cnt m h)))) (omega))
  (case exn
    (have hv (Acct.HasTy (List.nil Acct.Ty) v Acct.Ty.dat Bool.false)) (exact (Acct.ok-exn-v _ _ _ _ _ h1))
    (have hvc (forall [m :- Nat] (= Nat (Acct.cnt m v) 0))) (intro m) (exact (Acct.ok-exn-c _ _ _ _ _ h1 m))
    (show (Acct.OK s (Acct.Tm.try_ b h) A (Bool.or e1 e2) (Acct.Out.next s (Acct.subst 0 v h))))
    (apply (Acct.OK.next _ _ _ _ _ _ e2))
    (exact (Acct.subst-ty _ _ _ _ hh 0 Acct.Ty.dat v (Eq.refl _) hv (Acct.closed0 v Acct.Ty.dat Bool.false hv) (fn [q :- (= Bool (Acct.unr Acct.Ty.dat) Bool.true)] hvc)))
    (intro q) (exact (Acct.or-r2 _ _ q))
    (apply Acct.pure-rel) (exact hi) (intro m)
    (rw [(Acct.cnt-subst-0 m v (hvc m) h 0)])
    (show (<= (Acct.cnt m h) (+ (Acct.cnt m b) (Acct.cnt m h)))) (omega))
  (all_goals (exact FR)))

(a/theorem Acct.handling-eff [s :- Acct.Store, ops :- (List Nat), b :- Acct.Tm, r :- Acct.Tm, o :- Acct.Tm, B :- Acct.Ty,
                           e2 :- Bool, e3 :- Bool, op :- Nat, v :- Acct.Tm, k :- Acct.Tm, ek :- Bool,
                           hr :- (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) r B e2),
                           ho :- (Acct.HasTy (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                       (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) o B e3),
                           hfr :- (Acct.Tf 1 (List.nil Acct.Ty) r), hfo :- (Acct.Tf 3 (List.nil Acct.Ty) o),
                           hv :- (Acct.HasTy (List.nil Acct.Ty) v Acct.Ty.dat Bool.false),
                           hvc :- (forall [m :- Nat] (= Nat (Acct.cnt m v) 0)),
                           hk :- (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) k Acct.Ty.dat ek),
                           hkc :- (forall [m :- Nat] (= Nat (Acct.cnt m k) 0)),
                           hi :- (Acct.Inv s (Acct.Tm.handling ops b r o))]
  (Acct.OK s (Acct.Tm.handling ops b r o) B Bool.true (Acct.handleEff s ops r o op v k))
  (have HK (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) (Acct.Tm.handling ops k r o) B Bool.true))
  (exact (Acct.HasTy.handling (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) ops k r o B ek e2 e3 hk
           (Acct.weaken (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) r B e2 hr (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))
           (Acct.weaken (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true) (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) o B e3 ho (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))
           (Acct.tf-weaken1 1 r B e2 (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) hfr hr (Eq.refl _))
           (Acct.tf-weaken1 3 o B e3 (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true) (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) hfo ho (Eq.refl _))))
  (have CK (forall [m :- Nat] (= Nat (Acct.cnt m (Acct.Tm.handling ops k r o)) 0)))
  (intro m) (show (= Nat (+ (Acct.cnt m k) (+ (Acct.cnt m r) (Acct.cnt m o))) 0))
  (rw [(hkc m), (Acct.tf-c _ _ _ hfr m), (Acct.tf-c _ _ _ hfo m)])
  (unfold Acct.handleEff)
  (cases q (Acct.member op ops))
  (all_goals (try (dsimp only)))
  (exact (Acct.OK.eff s (Acct.Tm.handling ops b r o) B Bool.true op v (Acct.Tm.handling ops k r o) Bool.true (Eq.refl _) hv hvc HK CK))
  (have HK1 (Acct.HasTy (List.nil Acct.Ty) (Acct.Tm.lam (Acct.Tm.handling ops k r o)) (Acct.Ty.arr Acct.Ty.dat B Bool.true) Bool.false))
  (exact (Acct.HasTy.lam (List.nil Acct.Ty) Acct.Ty.dat B Bool.true (Acct.Tm.handling ops k r o) HK
           (fn [q :- (= Bool (Acct.unr Acct.Ty.dat) Bool.false)] (absurd q Acct.tt-ff)) (Acct.tf-nil 1 _ CK)))
  (have T1 (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))
             (Acct.subst 0 (Acct.Tm.lam (Acct.Tm.handling ops k r o)) o) B e3))
  (exact (Acct.subst-ty _ _ _ _ ho 0 (Acct.Ty.arr Acct.Ty.dat B Bool.true) (Acct.Tm.lam (Acct.Tm.handling ops k r o)) (Eq.refl _) HK1
           (Acct.closed0 _ _ _ HK1) (fn [q :- (= Bool (Acct.unr (Acct.Ty.arr Acct.Ty.dat B Bool.true)) Bool.true)] CK)))
  (have T2 (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty))
             (Acct.subst 0 v (Acct.subst 0 (Acct.Tm.lam (Acct.Tm.handling ops k r o)) o)) B e3))
  (exact (Acct.subst-ty _ _ _ _ T1 0 Acct.Ty.dat v (Eq.refl _) hv (Acct.closed0 _ _ _ hv) (fn [q :- (= Bool (Acct.unr Acct.Ty.dat) Bool.true)] hvc)))
  (have T3 (Acct.HasTy (List.nil Acct.Ty)
             (Acct.subst 0 (Acct.Tm.lit (Acct.Datum.num op)) (Acct.subst 0 v (Acct.subst 0 (Acct.Tm.lam (Acct.Tm.handling ops k r o)) o))) B e3))
  (exact (Acct.subst-ty _ _ _ _ T2 0 Acct.Ty.dat (Acct.Tm.lit (Acct.Datum.num op)) (Eq.refl _) (Acct.HasTy.lit (List.nil Acct.Ty) (Acct.Datum.num op))
           (fn [i :- Nat] (Eq.refl _)) (fn [q :- (= Bool (Acct.unr Acct.Ty.dat) Bool.true)] (fn [m :- Nat] (Eq.refl _)))))
  (have CKl (forall [m :- Nat] (= Nat (Acct.cnt m (Acct.Tm.lam (Acct.Tm.handling ops k r o))) 0))) (intro m) (exact (CK m))
  (apply (Acct.OK.next _ _ _ _ _ _ e3))
  (exact T3)
  (intro q) (rfl)
  (apply Acct.pure-rel) (exact hi) (intro m)
  (have z0 (= Nat (Acct.cnt m (Acct.Tm.lit (Acct.Datum.num op))) 0)) (rfl)
  (rw [(Acct.cnt-subst-0 m _ z0 _ 0), (Acct.cnt-subst-0 m v (hvc m) _ 0), (Acct.cnt-subst-0 m _ (CKl m) o 0), (Acct.tf-c _ _ _ hfo m)])
  (omega))

(a/theorem Acct.handling-ok [s :- Acct.Store, ops :- (List Nat), b :- Acct.Tm, r :- Acct.Tm, o :- Acct.Tm, B :- Acct.Ty,
                          e1 :- Bool, e2 :- Bool, e3 :- Bool,
                          hb :- (Acct.HasTy (List.nil Acct.Ty) b Acct.Ty.dat e1),
                          hr :- (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) r B e2),
                          ho :- (Acct.HasTy (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                      (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) o B e3),
                          hfr :- (Acct.Tf 1 (List.nil Acct.Ty) r), hfo :- (Acct.Tf 3 (List.nil Acct.Ty) o),
                          hi :- (Acct.Inv s (Acct.Tm.handling ops b r o)), o1 :- Acct.Out,
                          h1 :- (Acct.OK s b Acct.Ty.dat e1 o1),
                          hv1 :- (=> (= Acct.Out o1 Acct.Out.val) (= Bool (Acct.isVal b) Bool.true))]
  (Acct.OK s (Acct.Tm.handling ops b r o) B Bool.true (Acct.handlingOut s ops r o o1 b))
  (have FR (Acct.OK s (Acct.Tm.handling ops b r o) B Bool.true (Acct.frame o1 (fn [y :- Acct.Tm] (Acct.Tm.handling ops y r o)))))
  (apply (Acct.frame-ok s b Acct.Ty.dat e1 o1 (fn [y :- Acct.Tm] (Acct.Tm.handling ops y r o)) (fn [m :- Nat] (+ (Acct.cnt m r) (Acct.cnt m o))) B Bool.true (fn [f :- Bool] Bool.true) (fn [f :- Bool] Bool.true)))
  (intro m) (intro y) (rfl)
  (exact hi)
  (exact h1)
  (intro y) (intro f2) (intro hy) (intro hf2) (exact (Acct.HasTy.handling (List.nil Acct.Ty) ops y r o B f2 e2 e3 hy hr ho hfr hfo))
  (intro f2) (intro hf2) (intro q) (rfl)
  (intro he1) (intro k) (intro ek) (intro hk)
  (exact (Acct.HasTy.handling (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) ops k r o B ek e2 e3 hk
           (Acct.weaken (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) r B e2 hr (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))
           (Acct.weaken (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true) (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) o B e3 ho (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))
           (Acct.tf-weaken1 1 r B e2 (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) hfr hr (Eq.refl _))
           (Acct.tf-weaken1 3 o B e3 (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true) (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) hfo ho (Eq.refl _))))
  (intro he1) (intro m) (show (= Nat (+ (Acct.cnt m r) (Acct.cnt m o)) 0)) (rw [(Acct.tf-c _ _ _ hfr m), (Acct.tf-c _ _ _ hfo m)])
  (intro he1) (rfl)
  (cases o1)
  (case val
    (have vb (= Bool (Acct.isVal b) Bool.true)) (exact (hv1 (Eq.refl _)))
    (have e10 (= Bool e1 Bool.false)) (exact (Acct.val-eff _ _ _ _ hb vb))
    (have hb0 (Acct.HasTy (List.nil Acct.Ty) b Acct.Ty.dat Bool.false)) (rw [e10] at hb) (exact hb)
    (have cb (forall [m :- Nat] (= Nat (Acct.cnt m b) 0))) (intro m) (exact (Acct.val-unr-cnt b Acct.Ty.dat Bool.false hb0 vb (Eq.refl _) m))
    (show (Acct.OK s (Acct.Tm.handling ops b r o) B Bool.true (Acct.Out.next s (Acct.subst 0 b r))))
    (apply (Acct.OK.next _ _ _ _ _ _ e2))
    (exact (Acct.subst-ty _ _ _ _ hr 0 Acct.Ty.dat b (Eq.refl _) hb0 (Acct.closed0 _ _ _ hb0) (fn [q :- (= Bool (Acct.unr Acct.Ty.dat) Bool.true)] cb)))
    (intro q) (rfl)
    (apply Acct.pure-rel) (exact hi) (intro m)
    (rw [(Acct.cnt-subst-0 m b (cb m) r 0)])
    (show (<= (Acct.cnt m r) (+ (Acct.cnt m b) (+ (Acct.cnt m r) (Acct.cnt m o))))) (omega))
  (case eff
    (cases h1)
    (exact (Acct.handling-eff _ ops _ r o B e2 e3 _ _ _ _ hr ho hfr hfo hv hvc hk hkc hi)))
  (all_goals (exact FR)))

(a/theorem Acct.app-ev [s :- Acct.Store, f :- Acct.Tm, x :- Acct.Tm, A :- Acct.Ty, B :- Acct.Ty, e1 :- Bool, e2 :- Bool, e3 :- Bool,
                     hf :- (Acct.HasTy (List.nil Acct.Ty) f (Acct.Ty.arr A B e3) e1), hx :- (Acct.HasTy (List.nil Acct.Ty) x A e2),
                     hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 0 (List.nil Acct.Ty) x)), hi :- (Acct.Inv s (Acct.Tm.app f x)),
                     h1 :- (Acct.OK s f (Acct.Ty.arr A B e3) e1 (Acct.ev Bool.true s f)), h2 :- (Acct.OK s x A e2 (Acct.ev Bool.true s x))]
  (Acct.OK s (Acct.Tm.app f x) B (Bool.or e1 (Bool.or e2 e3)) (Acct.ev Bool.true s (Acct.Tm.app f x)))
  (exact (Acct.app-ok s f x A B e1 e2 e3 hf hx hs hi (Acct.ev Bool.true s f) (Acct.ev Bool.true s x) h1
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s f) Acct.Out.val)] h2)
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s f) Acct.Out.val)] (Acct.ev-val Bool.true s f q))
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s x) Acct.Out.val)] (Acct.ev-val Bool.true s x q)))))

(a/theorem Acct.let-ev [s :- Acct.Store, e :- Acct.Tm, b :- Acct.Tm, A :- Acct.Ty, B :- Acct.Ty, e1 :- Bool, e2 :- Bool,
                     he :- (Acct.HasTy (List.nil Acct.Ty) e A e1), hb :- (Acct.HasTy (List.cons Acct.Ty A (List.nil Acct.Ty)) b B e2),
                     hl :- (=> (= Bool (Acct.unr A) Bool.false) (<= (Acct.occ 0 b) 1)),
                     hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 1 (List.nil Acct.Ty) b)), hi :- (Acct.Inv s (Acct.Tm.let_ e b)),
                     h1 :- (Acct.OK s e A e1 (Acct.ev Bool.true s e))]
  (Acct.OK s (Acct.Tm.let_ e b) B (Bool.or e1 e2) (Acct.ev Bool.true s (Acct.Tm.let_ e b)))
  (exact (Acct.let-ok s e b A B e1 e2 he hb hl hs hi (Acct.ev Bool.true s e) h1
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s e) Acct.Out.val)] (Acct.ev-val Bool.true s e q)))))

(a/theorem Acct.spend-ev [s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm, e1 :- Bool,
                       hu :- (Acct.HasTy (List.nil Acct.Ty) u Acct.Ty.tok e1), hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat Bool.false),
                       hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 0 (List.nil Acct.Ty) x)), hi :- (Acct.Inv s (Acct.Tm.spend u x)),
                       h1 :- (Acct.OK s u Acct.Ty.tok e1 (Acct.ev Bool.true s u)), h2 :- (Acct.OK s x Acct.Ty.dat Bool.false (Acct.ev Bool.true s x))]
  (Acct.OK s (Acct.Tm.spend u x) Acct.Ty.tok e1 (Acct.ev Bool.true s (Acct.Tm.spend u x)))
  (exact (Acct.spend-ok s u x e1 hu hx hs hi (Acct.ev Bool.true s u) (Acct.ev Bool.true s x) h1
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s u) Acct.Out.val)] h2)
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s u) Acct.Out.val)] (Acct.ev-val Bool.true s u q)))))

(a/theorem Acct.join-ev [s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm, e1 :- Bool,
                      hu :- (Acct.HasTy (List.nil Acct.Ty) u Acct.Ty.tok e1), hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.tok Bool.false),
                      hs :- (=> (= Bool e1 Bool.true) (Acct.Tf 0 (List.nil Acct.Ty) x)), hi :- (Acct.Inv s (Acct.Tm.join u x)),
                      h1 :- (Acct.OK s u Acct.Ty.tok e1 (Acct.ev Bool.true s u)), h2 :- (Acct.OK s x Acct.Ty.tok Bool.false (Acct.ev Bool.true s x))]
  (Acct.OK s (Acct.Tm.join u x) Acct.Ty.tok e1 (Acct.ev Bool.true s (Acct.Tm.join u x)))
  (exact (Acct.join-ok s u x e1 hu hx hs hi (Acct.ev Bool.true s u) (Acct.ev Bool.true s x) h1
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s u) Acct.Out.val)] h2)
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s u) Acct.Out.val)] (Acct.ev-val Bool.true s u q))
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s x) Acct.Out.val)] (Acct.ev-val Bool.true s x q)))))

(a/theorem Acct.put-ev [s :- Acct.Store, u :- Acct.Tm, e1 :- Bool, hu :- (Acct.HasTy (List.nil Acct.Ty) u Acct.Ty.tok e1),
                     hi :- (Acct.Inv s (Acct.Tm.put u)), h1 :- (Acct.OK s u Acct.Ty.tok e1 (Acct.ev Bool.true s u))]
  (Acct.OK s (Acct.Tm.put u) Acct.Ty.dat e1 (Acct.ev Bool.true s (Acct.Tm.put u)))
  (exact (Acct.put-ok s u e1 hu hi (Acct.ev Bool.true s u) h1 (fn [q :- (= Acct.Out (Acct.ev Bool.true s u) Acct.Out.val)] (Acct.ev-val Bool.true s u q)))))

(a/theorem Acct.raise-ev [s :- Acct.Store, x :- Acct.Tm, A :- Acct.Ty, e1 :- Bool, hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat e1),
                       hi :- (Acct.Inv s (Acct.Tm.raise x)), h1 :- (Acct.OK s x Acct.Ty.dat e1 (Acct.ev Bool.true s x))]
  (Acct.OK s (Acct.Tm.raise x) A e1 (Acct.ev Bool.true s (Acct.Tm.raise x)))
  (exact (Acct.raise-ok s x A e1 hx hi (Acct.ev Bool.true s x) h1 (fn [q :- (= Acct.Out (Acct.ev Bool.true s x) Acct.Out.val)] (Acct.ev-val Bool.true s x q)))))

(a/theorem Acct.perform-ev [s :- Acct.Store, op :- Nat, x :- Acct.Tm, e1 :- Bool, hx :- (Acct.HasTy (List.nil Acct.Ty) x Acct.Ty.dat e1),
                         hi :- (Acct.Inv s (Acct.Tm.perform op x)), h1 :- (Acct.OK s x Acct.Ty.dat e1 (Acct.ev Bool.true s x))]
  (Acct.OK s (Acct.Tm.perform op x) Acct.Ty.dat Bool.true (Acct.ev Bool.true s (Acct.Tm.perform op x)))
  (exact (Acct.perform-ok s op x e1 hx hi (Acct.ev Bool.true s x) h1 (fn [q :- (= Acct.Out (Acct.ev Bool.true s x) Acct.Out.val)] (Acct.ev-val Bool.true s x q)))))

(a/theorem Acct.handling-ev [s :- Acct.Store, ops :- (List Nat), b :- Acct.Tm, r :- Acct.Tm, o :- Acct.Tm, B :- Acct.Ty, e1 :- Bool, e2 :- Bool, e3 :- Bool,
                          hb :- (Acct.HasTy (List.nil Acct.Ty) b Acct.Ty.dat e1),
                          hr :- (Acct.HasTy (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)) r B e2),
                          ho :- (Acct.HasTy (List.cons Acct.Ty (Acct.Ty.arr Acct.Ty.dat B Bool.true)
                                      (List.cons Acct.Ty Acct.Ty.dat (List.cons Acct.Ty Acct.Ty.dat (List.nil Acct.Ty)))) o B e3),
                          hfr :- (Acct.Tf 1 (List.nil Acct.Ty) r), hfo :- (Acct.Tf 3 (List.nil Acct.Ty) o),
                          hi :- (Acct.Inv s (Acct.Tm.handling ops b r o)), h1 :- (Acct.OK s b Acct.Ty.dat e1 (Acct.ev Bool.true s b))]
  (Acct.OK s (Acct.Tm.handling ops b r o) B Bool.true (Acct.ev Bool.true s (Acct.Tm.handling ops b r o)))
  (exact (Acct.handling-ok s ops b r o B e1 e2 e3 hb hr ho hfr hfo hi (Acct.ev Bool.true s b) h1
           (fn [q :- (= Acct.Out (Acct.ev Bool.true s b) Acct.Out.val)] (Acct.ev-val Bool.true s b q)))))

(a/theorem Acct.ev-ok [t :- Acct.Tm]
  (forall [s :- Acct.Store] (forall [A :- Acct.Ty] (forall [ef :- Bool]
    (=> (Acct.HasTy (List.nil Acct.Ty) t A ef) (=> (Acct.Inv s t) (Acct.OK s t A ef (Acct.ev Bool.true s t)))))))
  (induction t)
  (all_goals (intro s) (intro A0) (intro ef) (intro ht) (intro hi))
  (case var (cases ht) (simp only [Acct.ctx] at h) (cases h))
  (case lit (exact (Acct.OK.val s _ A0 ef)))
  (case lam (exact (Acct.OK.val s _ A0 ef)))
  (case tok (exact (Acct.OK.val s _ A0 ef)))
  (case app
    (have IF (Acct.Inv s f)) (apply (Acct.inv-le s (Acct.Tm.app f x) f hi)) (intro m) (show (<= (Acct.cnt m f) (+ (Acct.cnt m f) (Acct.cnt m x)))) (omega)
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.app f x) x hi)) (intro m) (show (<= (Acct.cnt m x) (+ (Acct.cnt m f) (Acct.cnt m x)))) (omega)
    (cases ht)
    (exact (Acct.app-ev s _ _ _ _ _ _ _ hf hx hs hi (ih_f s _ _ hf IF) (ih_x s _ _ hx IX))))
  (case let_
    (have IE (Acct.Inv s e)) (apply (Acct.inv-le s (Acct.Tm.let_ e b) e hi)) (intro m) (show (<= (Acct.cnt m e) (+ (Acct.cnt m e) (Acct.cnt m b)))) (omega)
    (cases ht)
    (exact (Acct.let-ev s _ _ _ _ _ _ he hb hl hs hi (ih_e s _ _ he IE))))
  (case if_
    (have IC (Acct.Inv s c)) (apply (Acct.inv-le s (Acct.Tm.if_ c u e) c hi)) (intro m) (show (<= (Acct.cnt m c) (+ (Acct.cnt m c) (Acct.mx (Acct.cnt m u) (Acct.cnt m e))))) (omega)
    (cases ht)
    (exact (Acct.if-ok s _ _ _ _ _ _ _ hc hu he hs hi _ (ih_c s _ _ hc IC))))
  (case take
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.take x) x hi)) (intro m) (exact (Nat.le_refl _))
    (cases ht)
    (exact (Acct.take-ok s _ _ hx hi _ (ih_x s _ _ hx IX))))
  (case spend
    (have IU (Acct.Inv s u)) (apply (Acct.inv-le s (Acct.Tm.spend u x) u hi)) (intro m) (show (<= (Acct.cnt m u) (+ (Acct.cnt m u) (Acct.cnt m x)))) (omega)
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.spend u x) x hi)) (intro m) (show (<= (Acct.cnt m x) (+ (Acct.cnt m u) (Acct.cnt m x)))) (omega)
    (cases ht)
    (exact (Acct.spend-ev s _ _ _ hu hx hs hi (ih_u s _ _ hu IU) (ih_x s _ _ hx IX))))
  (case join
    (have IU (Acct.Inv s u)) (apply (Acct.inv-le s (Acct.Tm.join u v) u hi)) (intro m) (show (<= (Acct.cnt m u) (+ (Acct.cnt m u) (Acct.cnt m v)))) (omega)
    (have IV (Acct.Inv s v)) (apply (Acct.inv-le s (Acct.Tm.join u v) v hi)) (intro m) (show (<= (Acct.cnt m v) (+ (Acct.cnt m u) (Acct.cnt m v)))) (omega)
    (cases ht)
    (exact (Acct.join-ev s _ _ _ hu hv hs hi (ih_u s _ _ hu IU) (ih_v s _ _ hv IV))))
  (case put
    (have IU (Acct.Inv s u)) (apply (Acct.inv-le s (Acct.Tm.put u) u hi)) (intro m) (exact (Nat.le_refl _))
    (cases ht)
    (exact (Acct.put-ev s _ _ hu hi (ih_u s _ _ hu IU))))
  (case raise
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.raise x) x hi)) (intro m) (exact (Nat.le_refl _))
    (cases ht)
    (exact (Acct.raise-ev s _ _ _ hx hi (ih_x s _ _ hx IX))))
  (case try_
    (have IB (Acct.Inv s b)) (apply (Acct.inv-le s (Acct.Tm.try_ b h) b hi)) (intro m) (show (<= (Acct.cnt m b) (+ (Acct.cnt m b) (Acct.cnt m h)))) (omega)
    (cases ht)
    (exact (Acct.try-ok s _ _ _ _ _ hb hh hs hi _ (ih_b s _ _ hb IB))))
  (case perform
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.perform op x) x hi)) (intro m) (exact (Nat.le_refl _))
    (cases ht)
    (exact (Acct.perform-ev s _ _ _ hx hi (ih_x s _ _ hx IX))))
  (case handle (cases ht) (exact (Acct.handle-ok s _ _ _ _ _ _ _ _ hb hr ho hfr hfo hi)))
  (case handling
    (have IB (Acct.Inv s b)) (apply (Acct.inv-le s (Acct.Tm.handling ops b r o) b hi)) (intro m) (show (<= (Acct.cnt m b) (+ (Acct.cnt m b) (+ (Acct.cnt m r) (Acct.cnt m o))))) (omega)
    (cases ht)
    (exact (Acct.handling-ev s _ _ _ _ _ _ _ _ hb hr ho hfr hfo hi (ih_b s _ _ hb IB)))))

(a/inductive Acct.Good [] :in Prop :indices [s Acct.Store t Acct.Tm A Acct.Ty]
  (mk [s Acct.Store] [t Acct.Tm] [A Acct.Ty] [e Bool] [ht (Acct.HasTy (List.nil Acct.Ty) t A e)] [hi (Acct.Inv s t)]
      :where [s t A]))

(a/theorem Acct.ok-step [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, e :- Bool, o :- Acct.Out, s2 :- Acct.Store, t2 :- Acct.Tm,
                      hi :- (Acct.Inv s t), ho :- (Acct.OK s t A e o),
                      h :- (= (Option Acct.Config) (Acct.stepOut o) (Option.some Acct.Config (Acct.Config.mk s2 t2)))]
  (Acct.Good s2 t2 A)
  (cases ho)
  (all_goals (simp [Acct.stepOut] at h))
  (all_goals (cases h))
  (exact (Acct.Good.mk _ _ _ _ ht (Acct.inv-step _ _ _ _ hi hr))))

(a/theorem Acct.preservation [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, s2 :- Acct.Store, t2 :- Acct.Tm,
                           hg :- (Acct.Good s t A),
                           h :- (= (Option Acct.Config) (Acct.step (Acct.Config.mk s t)) (Option.some Acct.Config (Acct.Config.mk s2 t2)))]
  (Acct.Good s2 t2 A)
  (cases hg)
  (simp only [Acct.step] at h)
  (exact (Acct.ok-step _ _ _ _ _ _ _ hi (Acct.ev-ok _ _ _ _ ht hi) h)))

(a/inductive Acct.Progress [] :in Prop :indices [s Acct.Store t Acct.Tm]
  (value [s Acct.Store] [t Acct.Tm] [h (= Acct.Out (Acct.ev Bool.true s t) Acct.Out.val)] :where [s t])
  (steps [s Acct.Store] [t Acct.Tm] [s2 Acct.Store] [t2 Acct.Tm]
         [h (= (Option Acct.Config) (Acct.step (Acct.Config.mk s t)) (Option.some Acct.Config (Acct.Config.mk s2 t2)))] :where [s t])
  (unhandled [s Acct.Store] [t Acct.Tm] [op Nat] [v Acct.Tm] [k Acct.Tm]
             [h (= Acct.Out (Acct.ev Bool.true s t) (Acct.Out.eff op v k))] :where [s t])
  (uncaught [s Acct.Store] [t Acct.Tm] [v Acct.Tm] [h (= Acct.Out (Acct.ev Bool.true s t) (Acct.Out.exn v))] :where [s t])
  (stuck [s Acct.Store] [t Acct.Tm] [st Acct.Stuck] [h (= Acct.Out (Acct.ev Bool.true s t) (Acct.Out.stuck st))]
         [h1 (Not (= Acct.Stuck st Acct.Stuck.reuse))] [h2 (Not (= Acct.Stuck st Acct.Stuck.scope))] :where [s t]))

(a/theorem Acct.step-of [s :- Acct.Store, t :- Acct.Tm, s2 :- Acct.Store, t2 :- Acct.Tm,
                      h :- (= Acct.Out (Acct.ev Bool.true s t) (Acct.Out.next s2 t2))]
  (= (Option Acct.Config) (Acct.step (Acct.Config.mk s t)) (Option.some Acct.Config (Acct.Config.mk s2 t2)))
  (show (= (Option Acct.Config) (Acct.stepOut (Acct.ev Bool.true s t)) (Option.some Acct.Config (Acct.Config.mk s2 t2))))
  (rw [h]))

(a/theorem Acct.ok-progress [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, e :- Bool, o :- Acct.Out,
                          ho :- (Acct.OK s t A e o), hq :- (= Acct.Out (Acct.ev Bool.true s t) o)]
  (Acct.Progress s t)
  (cases ho)
  (exact (Acct.Progress.value _ _ hq))
  (exact (Acct.Progress.steps _ _ _ _ (Acct.step-of _ _ _ _ hq)))
  (exact (Acct.Progress.unhandled _ _ _ _ _ hq))
  (exact (Acct.Progress.uncaught _ _ _ hq))
  (exact (Acct.Progress.stuck _ _ _ hq h1 h2)))

(a/theorem Acct.progress [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, hg :- (Acct.Good s t A)]
  (Acct.Progress s t)
  (cases hg)
  (exact (Acct.ok-progress _ _ _ _ _ (Acct.ev-ok _ _ _ _ ht hi) (Eq.refl _))))

(a/theorem Acct.no-reuse [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, hg :- (Acct.Good s t A)]
  (Not (= Acct.Out (Acct.ev Bool.true s t) (Acct.Out.stuck Acct.Stuck.reuse)))
  (cases hg)
  (intro h)
  (have ok (Acct.OK s t A e (Acct.Out.stuck Acct.Stuck.reuse))) (rw [(Eq.symm h)]) (exact (Acct.ev-ok _ _ _ _ ht hi))
  (cases ok) (exact (h1 (Eq.refl _))))

(a/theorem Acct.held-erase [l :- Acct.Live, i :- Nat, h :- (= Bool (Acct.isLive l i) Bool.true)]
  (= (Option Nat) (Acct.held Bool.false l i) (Acct.held Bool.true l i))
  (have f (= (Option Nat) (Acct.find l i) (Option.some Nat (Acct.amt l i)))) (exact (Acct.find-live l i h))
  (unfold Acct.held) (try (dsimp only)) (rw [f]))

(a/theorem Acct.live-of-cnt [s :- Acct.Store, t :- Acct.Tm, i :- Nat, hi :- (Acct.Inv s t), c :- (<= 1 (Acct.cnt i t))]
  (= Bool (Acct.isLive (Acct.lv s) i) Bool.true)
  (have u (<= (Acct.cnt i t) 1)) (exact (Acct.inv-1 _ _ hi i))
  (have c1 (= Nat (Acct.cnt i t) 1)) (omega)
  (exact (Acct.inv-2 _ _ hi i c1)))

(a/theorem Acct.spendStep-erase [s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm, hi :- (Acct.Inv s (Acct.Tm.spend u x))]
  (= Acct.Out (Acct.spendStep Bool.false s u x) (Acct.spendStep Bool.true s u x))
  (cases u)
  (all_goals (try (rfl)))
  (have lv (= Bool (Acct.isLive (Acct.lv s) i) Bool.true)) (apply (Acct.live-of-cnt _ _ i hi)) (simp [Acct.cnt])
  (cases s)
  (show (= Acct.Out (Acct.spendN Bool.false (Acct.Store.mk wallet spent next live) i x) (Acct.spendN Bool.true (Acct.Store.mk wallet spent next live) i x)))
  (unfold Acct.spendN)
  (cases qa (Acct.amount x))
  (all_goals (try (dsimp only)))
  (show (= Acct.Out (Acct.spendH (Acct.Store.mk wallet spent next live) i val (Acct.held Bool.false live i))
                    (Acct.spendH (Acct.Store.mk wallet spent next live) i val (Acct.held Bool.true live i))))
  (rw [(Acct.held-erase live i lv)]))

(a/theorem Acct.putStep-erase [s :- Acct.Store, u :- Acct.Tm, hi :- (Acct.Inv s (Acct.Tm.put u))]
  (= Acct.Out (Acct.putStep Bool.false s u) (Acct.putStep Bool.true s u))
  (cases u)
  (all_goals (try (rfl)))
  (have lv (= Bool (Acct.isLive (Acct.lv s) i) Bool.true)) (apply (Acct.live-of-cnt _ _ i hi)) (simp [Acct.cnt])
  (cases s)
  (show (= Acct.Out (Acct.putH (Acct.Store.mk wallet spent next live) i (Acct.held Bool.false live i)) (Acct.putH (Acct.Store.mk wallet spent next live) i (Acct.held Bool.true live i))))
  (rw [(Acct.held-erase live i lv)]))

(a/theorem Acct.joinN-erase [s :- Acct.Store, i :- Nat, j :- Nat, hi :- (Acct.Inv s (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j)))]
  (= Acct.Out (Acct.joinN Bool.false s i j) (Acct.joinN Bool.true s i j))
  (have ne (Not (= Nat i j)))
  (intro z) (have uu (<= (Acct.cnt i (Acct.Tm.join (Acct.Tm.tok i) (Acct.Tm.tok j))) 1)) (exact (Acct.inv-1 _ _ hi i))
  (rw [z] at uu) (simp [Acct.cnt] at uu)
  (have lvi (= Bool (Acct.isLive (Acct.lv s) i) Bool.true)) (apply (Acct.live-of-cnt _ _ i hi)) (simp [Acct.cnt])
  (have lvj (= Bool (Acct.isLive (Acct.lv s) j) Bool.true)) (apply (Acct.live-of-cnt _ _ j hi)) (simp [Acct.cnt])
  (cases s)
  (unfold Acct.joinN) (rw [(Acct.beq-ne i j ne)]) (try (dsimp only))
  (show (= Acct.Out (Acct.joinH (Acct.Store.mk wallet spent next live) i j (Acct.held Bool.false live i) (Acct.held Bool.false live j))
                    (Acct.joinH (Acct.Store.mk wallet spent next live) i j (Acct.held Bool.true live i) (Acct.held Bool.true live j))))
  (rw [(Acct.held-erase live i lvi), (Acct.held-erase live j lvj)]))

(a/theorem Acct.joinStep-erase [s :- Acct.Store, u :- Acct.Tm, v :- Acct.Tm, hi :- (Acct.Inv s (Acct.Tm.join u v))]
  (= Acct.Out (Acct.joinStep Bool.false s u v) (Acct.joinStep Bool.true s u v))
  (cases u) (all_goals (cases v)) (all_goals (try (rfl)))
  (exact (Acct.joinN-erase _ _ _ hi)))

(a/theorem Acct.ev-erase [t :- Acct.Tm]
  (forall [s :- Acct.Store] (=> (Acct.Inv s t) (= Acct.Out (Acct.ev Bool.false s t) (Acct.ev Bool.true s t))))
  (induction t)
  (all_goals (intro s) (intro hi))
  (case var (rfl)) (case lit (rfl)) (case lam (rfl)) (case tok (rfl)) (case handle (rfl))
  (case app
    (have IF (Acct.Inv s f)) (apply (Acct.inv-le s (Acct.Tm.app f x) f hi)) (intro m) (show (<= (Acct.cnt m f) (+ (Acct.cnt m f) (Acct.cnt m x)))) (omega)
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.app f x) x hi)) (intro m) (show (<= (Acct.cnt m x) (+ (Acct.cnt m f) (Acct.cnt m x)))) (omega)
    (show (= Acct.Out (Acct.seq2 (Acct.ev Bool.false s f) (Acct.ev Bool.false s x) (fn [f2 :- Acct.Tm] (Acct.Tm.app f2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.app f x2)) (Acct.beta s f x))
                      (Acct.seq2 (Acct.ev Bool.true s f) (Acct.ev Bool.true s x) (fn [f2 :- Acct.Tm] (Acct.Tm.app f2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.app f x2)) (Acct.beta s f x))))
    (rw [(ih_f s IF), (ih_x s IX)]))
  (case let_
    (have IE (Acct.Inv s e)) (apply (Acct.inv-le s (Acct.Tm.let_ e b) e hi)) (intro m) (show (<= (Acct.cnt m e) (+ (Acct.cnt m e) (Acct.cnt m b)))) (omega)
    (show (= Acct.Out (Acct.seq1 (Acct.ev Bool.false s e) (fn [e2 :- Acct.Tm] (Acct.Tm.let_ e2 b)) (Acct.Out.next s (Acct.subst 0 e b)))
                      (Acct.seq1 (Acct.ev Bool.true s e) (fn [e2 :- Acct.Tm] (Acct.Tm.let_ e2 b)) (Acct.Out.next s (Acct.subst 0 e b)))))
    (rw [(ih_e s IE)]))
  (case if_
    (have IC (Acct.Inv s c)) (apply (Acct.inv-le s (Acct.Tm.if_ c u e) c hi)) (intro m) (show (<= (Acct.cnt m c) (+ (Acct.cnt m c) (Acct.mx (Acct.cnt m u) (Acct.cnt m e))))) (omega)
    (show (= Acct.Out (Acct.seq1 (Acct.ev Bool.false s c) (fn [q2 :- Acct.Tm] (Acct.Tm.if_ q2 u e)) (Acct.Out.next s (Acct.pick c u e)))
                      (Acct.seq1 (Acct.ev Bool.true s c) (fn [q2 :- Acct.Tm] (Acct.Tm.if_ q2 u e)) (Acct.Out.next s (Acct.pick c u e)))))
    (rw [(ih_c s IC)]))
  (case take
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.take x) x hi)) (intro m) (exact (Nat.le_refl _))
    (show (= Acct.Out (Acct.seq1 (Acct.ev Bool.false s x) (fn [x2 :- Acct.Tm] (Acct.Tm.take x2)) (Acct.takeStep s x))
                      (Acct.seq1 (Acct.ev Bool.true s x) (fn [x2 :- Acct.Tm] (Acct.Tm.take x2)) (Acct.takeStep s x))))
    (rw [(ih_x s IX)]))
  (case spend
    (have IU (Acct.Inv s u)) (apply (Acct.inv-le s (Acct.Tm.spend u x) u hi)) (intro m) (show (<= (Acct.cnt m u) (+ (Acct.cnt m u) (Acct.cnt m x)))) (omega)
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.spend u x) x hi)) (intro m) (show (<= (Acct.cnt m x) (+ (Acct.cnt m u) (Acct.cnt m x)))) (omega)
    (show (= Acct.Out (Acct.seq2 (Acct.ev Bool.false s u) (Acct.ev Bool.false s x) (fn [u2 :- Acct.Tm] (Acct.Tm.spend u2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.spend u x2)) (Acct.spendStep Bool.false s u x))
                      (Acct.seq2 (Acct.ev Bool.true s u) (Acct.ev Bool.true s x) (fn [u2 :- Acct.Tm] (Acct.Tm.spend u2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.spend u x2)) (Acct.spendStep Bool.true s u x))))
    (rw [(ih_u s IU), (ih_x s IX), (Acct.spendStep-erase s u x hi)]))
  (case join
    (have IU (Acct.Inv s u)) (apply (Acct.inv-le s (Acct.Tm.join u v) u hi)) (intro m) (show (<= (Acct.cnt m u) (+ (Acct.cnt m u) (Acct.cnt m v)))) (omega)
    (have IV (Acct.Inv s v)) (apply (Acct.inv-le s (Acct.Tm.join u v) v hi)) (intro m) (show (<= (Acct.cnt m v) (+ (Acct.cnt m u) (Acct.cnt m v)))) (omega)
    (show (= Acct.Out (Acct.seq2 (Acct.ev Bool.false s u) (Acct.ev Bool.false s v) (fn [u2 :- Acct.Tm] (Acct.Tm.join u2 v)) (fn [v2 :- Acct.Tm] (Acct.Tm.join u v2)) (Acct.joinStep Bool.false s u v))
                      (Acct.seq2 (Acct.ev Bool.true s u) (Acct.ev Bool.true s v) (fn [u2 :- Acct.Tm] (Acct.Tm.join u2 v)) (fn [v2 :- Acct.Tm] (Acct.Tm.join u v2)) (Acct.joinStep Bool.true s u v))))
    (rw [(ih_u s IU), (ih_v s IV), (Acct.joinStep-erase s u v hi)]))
  (case put
    (have IU (Acct.Inv s u)) (apply (Acct.inv-le s (Acct.Tm.put u) u hi)) (intro m) (exact (Nat.le_refl _))
    (show (= Acct.Out (Acct.seq1 (Acct.ev Bool.false s u) (fn [u2 :- Acct.Tm] (Acct.Tm.put u2)) (Acct.putStep Bool.false s u))
                      (Acct.seq1 (Acct.ev Bool.true s u) (fn [u2 :- Acct.Tm] (Acct.Tm.put u2)) (Acct.putStep Bool.true s u))))
    (rw [(ih_u s IU), (Acct.putStep-erase s u hi)]))
  (case raise
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.raise x) x hi)) (intro m) (exact (Nat.le_refl _))
    (show (= Acct.Out (Acct.seq1 (Acct.ev Bool.false s x) (fn [x2 :- Acct.Tm] (Acct.Tm.raise x2)) (Acct.Out.exn x))
                      (Acct.seq1 (Acct.ev Bool.true s x) (fn [x2 :- Acct.Tm] (Acct.Tm.raise x2)) (Acct.Out.exn x))))
    (rw [(ih_x s IX)]))
  (case try_
    (have IB (Acct.Inv s b)) (apply (Acct.inv-le s (Acct.Tm.try_ b h) b hi)) (intro m) (show (<= (Acct.cnt m b) (+ (Acct.cnt m b) (Acct.cnt m h)))) (omega)
    (show (= Acct.Out (Acct.tryOut s h (Acct.ev Bool.false s b) b) (Acct.tryOut s h (Acct.ev Bool.true s b) b)))
    (rw [(ih_b s IB)]))
  (case perform
    (have IX (Acct.Inv s x)) (apply (Acct.inv-le s (Acct.Tm.perform op x) x hi)) (intro m) (exact (Nat.le_refl _))
    (show (= Acct.Out (Acct.seq1 (Acct.ev Bool.false s x) (fn [x2 :- Acct.Tm] (Acct.Tm.perform op x2)) (Acct.Out.eff op x (Acct.Tm.var 0)))
                      (Acct.seq1 (Acct.ev Bool.true s x) (fn [x2 :- Acct.Tm] (Acct.Tm.perform op x2)) (Acct.Out.eff op x (Acct.Tm.var 0)))))
    (rw [(ih_x s IX)]))
  (case handling
    (have IB (Acct.Inv s b)) (apply (Acct.inv-le s (Acct.Tm.handling ops b r o) b hi)) (intro m) (show (<= (Acct.cnt m b) (+ (Acct.cnt m b) (+ (Acct.cnt m r) (Acct.cnt m o))))) (omega)
    (show (= Acct.Out (Acct.handlingOut s ops r o (Acct.ev Bool.false s b) b) (Acct.handlingOut s ops r o (Acct.ev Bool.true s b) b)))
    (rw [(ih_b s IB)])))

(a/theorem Acct.erasure [s :- Acct.Store, t :- Acct.Tm, hi :- (Acct.Inv s t)]
  (= (Option Acct.Config) (Acct.stepU (Acct.Config.mk s t)) (Acct.step (Acct.Config.mk s t)))
  (show (= (Option Acct.Config) (Acct.stepOut (Acct.ev Bool.false s t)) (Acct.stepOut (Acct.ev Bool.true s t))))
  (rw [(Acct.ev-erase t s hi)]))

(a/theorem Acct.erasure-good [s :- Acct.Store, t :- Acct.Tm, A :- Acct.Ty, hg :- (Acct.Good s t A)]
  (= (Option Acct.Config) (Acct.stepU (Acct.Config.mk s t)) (Acct.step (Acct.Config.mk s t)))
  (cases hg) (exact (Acct.erasure _ _ hi)))
