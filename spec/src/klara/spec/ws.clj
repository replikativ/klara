(ns klara.spec.ws
  "Well-scopedness and its basic lemmas."
  (:require [ansatz.core :as a]
            [klara.spec.core]))

;; WS n t: every free index of t is below n.
(a/inductive WS [] :in Prop :indices [n Nat t Tm]
  (var [n Nat] [i Nat] [h (LT.lt Nat instLTNat i n)] :where [n (Tm.var i)])
  (lit [n Nat] [d Datum] :where [n (Tm.lit d)])
  (lam [n Nat] [b Tm] [hb (WS (+ n 1) b)] :where [n (Tm.lam b)])
  (app [n Nat] [f Tm] [x Tm] [hf (WS n f)] [hx (WS n x)] :where [n (Tm.app f x)])
  (let_ [n Nat] [e Tm] [b Tm] [he (WS n e)] [hb (WS (+ n 1) b)] :where [n (Tm.let_ e b)])
  (if_ [n Nat] [c Tm] [u Tm] [e Tm] [hc (WS n c)] [hu (WS n u)] [he (WS n e)] :where [n (Tm.if_ c u e)])
  (letrec [n Nat] [fb Tm] [b Tm] [hfb (WS (+ n 2) fb)] [hb (WS (+ n 1) b)] :where [n (Tm.letrec fb b)])
  (resolve [n Nat] [id Nat] :where [n (Tm.resolve id)])
  (prim [n Nat] [op PrimOp] [x Tm] [y Tm] [hx (WS n x)] [hy (WS n y)] :where [n (Tm.prim op x y)])
  (perform [n Nat] [op Nat] [h Tm] [x Tm] [hh (WS n h)] [hx (WS n x)] :where [n (Tm.perform op h x)])
  (handle [n Nat] [b Tm] [r Tm] [o Tm] [hb (WS (+ n 1) b)] [hr (WS (+ n 1) r)] [ho (WS (+ n 3) o)]
          :where [n (Tm.handle b r o)])
  (specialize [n Nat] [p Tm] [m Tm] [hp (WS n p)] [hm (WS n m)] :where [n (Tm.specialize p m)])
  (fix [n Nat] [fb Tm] [hfb (WS (+ n 2) fb)] :where [n (Tm.fix fb)])
  (cap [n Nat] [l Nat] :where [n (Tm.cap l)])
  (handling [n Nat] [l Nat] [b Tm] [r Tm] [o Tm] [hb (WS n b)] [hr (WS (+ n 1) r)] [ho (WS (+ n 3) o)]
            :where [n (Tm.handling l b r o)]))

;; ---------------------------------------------------------------------------
;; Weakening

(a/theorem ws-weaken [n :- Nat, t :- Tm, h :- (WS n t)]
  (forall [m :- Nat] (=> (<= n m) (WS m t)))
  (induction h)
  (all_goals (intro m) (intro hm))
  (all_goals (constructor))
  (all_goals (try (omega)))
  (all_goals (first (apply ih_hb) (apply ih_hf) (apply ih_hx) (apply ih_he) (apply ih_hc) (apply ih_hu)
                    (apply ih_hfb) (apply ih_hy) (apply ih_hh) (apply ih_hr) (apply ih_ho) (apply ih_hp)
                    (apply ih_hm)))
  (all_goals (omega)))

(a/theorem ws-closed [t :- Tm, h :- (WS 0 t), m :- Nat]
  (WS m t)
  (apply (ws-weaken 0 t h m)) (omega))

;; ---------------------------------------------------------------------------
;; Substitution of a closed value

(a/theorem beq-false-ne [a :- Nat, b :- Nat, h :- (= (Nat.beq a b) false)] (Not (= a b))
  (grind))

(a/theorem blt-false-ge [a :- Nat, b :- Nat, h :- (= (Nat.blt a b) false)] (<= b a)
  (grind))

(a/theorem ws-substVar [v :- Tm, hv :- (WS 0 v), i :- Nat, n :- Nat, j :- Nat,
                        hi :- (< i (+ n 1)), hj :- (<= j n)]
  (WS n (substVar v i j))
  (simp [substVar])
  (split_ifs)
  (all_goals (try (dsimp)))
  (all_goals (try (apply (ws-closed v hv n))))
  (all_goals (constructor))
  (all_goals (simp_all [Nat.beq_eq, Nat.blt_eq]))
  (all_goals (try (omega)))
  (have h1 (Not (= i j))) (apply beq-false-ne) (assumption)
  (have h2 (<= i j)) (apply blt-false-ge) (assumption)
  (omega))

(a/theorem ws-var-inv [n :- Nat, i :- Nat, h :- (WS n (Tm.var i))] (< i n)
  (cases h) (assumption))

;; ansatz-specific: the var case is a separate lemma because after `cases`
;; the variable's name is inaccessible (no `rename_i`/`next` naming needed in Lean).
(a/theorem ws-substF-var [v :- Tm, hv :- (WS 0 v), i :- Nat, n :- Nat, j :- Nat,
                          h :- (WS (+ n 1) (Tm.var i)), hj :- (<= j n)]
  (WS n (substF v (Tm.var i) j))
  (exact (ws-substVar v hv i n j (ws-var-inv (+ n 1) i h) hj)))

(a/theorem ws-substF [v :- Tm, hv :- (WS 0 v), t :- Tm]
  (forall [n :- Nat] (forall [j :- Nat] (=> (WS (+ n 1) t) (=> (<= j n) (WS n (substF v t j))))))
  (induction t)
  (all_goals (intro n) (intro j) (intro h) (intro hj))
  (all_goals (try (apply ws-substF-var) (assumption) (assumption) (assumption)))
  (all_goals (cases h))
  (all_goals (simp [substF]))
  (all_goals (try (constructor)))
  (all_goals (try (first (apply ih_b) (apply ih_f) (apply ih_x) (apply ih_e) (apply ih_c) (apply ih_t)
                    (apply ih_fb) (apply ih_y) (apply ih_h) (apply ih_r) (apply ih_o) (apply ih_p)
                    (apply ih_m))))
  (all_goals (try (first (assumption) (omega)))))

(a/theorem ws-substF' [n :- Nat, j :- Nat, v :- Tm, t :- Tm,
                      hv :- (WS 0 v), ht :- (WS (+ n 1) t), hj :- (<= j n)]
  (WS n (substF v t j))
  (exact (ws-substF v hv t n j ht hj)))

(a/theorem ws-subst [n :- Nat, j :- Nat, v :- Tm, t :- Tm,
                     hv :- (WS 0 v), ht :- (WS (+ n 1) t), hj :- (<= j n)]
  (WS n (subst j v t))
  (exact (ws-substF v hv t n j ht hj)))

;; Substitution at or above the scope of a term is the identity.
(a/theorem substVar-closed [v :- Tm, i :- Nat, j :- Nat, hi :- (< i j)] (= Tm (substVar v i j) (Tm.var i))
  (simp [substVar])
  (split_ifs)
  (all_goals (try (dsimp)))
  (all_goals (simp_all [Nat.beq_eq, Nat.blt_eq]))
  (all_goals (try (omega))))

(a/theorem substF-closed-var [v :- Tm, i :- Nat, j :- Nat]
  (=> (WS j (Tm.var i)) (= Tm (substF v (Tm.var i) j) (Tm.var i)))
  (intro h)
  (have hi (< i j)) (exact (ws-var-inv j i h))
  (exact (substVar-closed v i j hi)))

(a/theorem substF-closed [v :- Tm, t :- Tm]
  (forall [j :- Nat] (=> (WS j t) (= Tm (substF v t j) t)))
  (induction t)
  (all_goals (intro j))
  (all_goals (try (apply substF-closed-var)))
  (all_goals (intro h))
  (all_goals (cases h))
  (all_goals (simp [substF]))
  (all_goals (try (simp_all))))
