(ns klara.formal.ws
  "Well-scopedness of formal terms and its basic lemmas: weakening,
  substitution of closed values, and soundness of the closedness check
  `run` performs (L2.run.closed)."
  (:require [ansatz.core :as a]
            [klara.formal.core]))

;; WS n t: every free de Bruijn index of t is below n.
(a/inductive WS [] :in Prop :indices [n Nat t Tm]
  (var [n Nat] [i Nat] [h (LT.lt Nat instLTNat i n)] :where [n (Tm.var i)])
  (lit [n Nat] [d Datum] :where [n (Tm.lit d)])
  (lam [n Nat] [b Tm] [hb (WS (+ n 1) b)] :where [n (Tm.lam b)])
  (app [n Nat] [f Tm] [x Tm] [hf (WS n f)] [hx (WS n x)] :where [n (Tm.app f x)])
  (let_ [n Nat] [e Tm] [b Tm] [he (WS n e)] [hb (WS (+ n 1) b)] :where [n (Tm.let_ e b)])
  (if_ [n Nat] [c Tm] [u Tm] [e Tm] [hc (WS n c)] [hu (WS n u)] [he (WS n e)] :where [n (Tm.if_ c u e)])
  (letrec [n Nat] [fb Tm] [b Tm] [hfb (WS (+ n 2) fb)] [hb (WS (+ n 1) b)] :where [n (Tm.letrec fb b)])
  (fix [n Nat] [fb Tm] [hfb (WS (+ n 2) fb)] :where [n (Tm.fix fb)])
  (glob [n Nat] [id Nat] :where [n (Tm.glob id)])
  (pin [n Nat] [w Nat] [id Nat] :where [n (Tm.pin w id)])
  (prim [n Nat] [op PrimOp] [x Tm] [y Tm] [hx (WS n x)] [hy (WS n y)] :where [n (Tm.prim op x y)])
  (perform [n Nat] [op Nat] [x Tm] [hx (WS n x)] :where [n (Tm.perform op x)])
  (handle [n Nat] [ops (List Nat)] [b Tm] [r Tm] [o Tm] [hb (WS n b)] [hr (WS (+ n 1) r)] [ho (WS (+ n 3) o)]
          :where [n (Tm.handle ops b r o)])
  (handling [n Nat] [ops (List Nat)] [b Tm] [r Tm] [o Tm] [hb (WS n b)] [hr (WS (+ n 1) r)] [ho (WS (+ n 3) o)]
            :where [n (Tm.handling ops b r o)])
  (code [n Nat] [u Tm] [hu (WS n u)] :where [n (Tm.code u)])
  (esc [n Nat] [u Tm] [hu (WS n u)] :where [n (Tm.esc u)])
  (run_ [n Nat] [u Tm] [hu (WS n u)] :where [n (Tm.run_ u)])
  (gvar [n Nat] [g Nat] :where [n (Tm.gvar g)])
  (nlam [n Nat] [g Nat] [b Tm] [hb (WS n b)] :where [n (Tm.nlam g b)])
  (nlet [n Nat] [g Nat] [e Tm] [b Tm] [he (WS n e)] [hb (WS n b)] :where [n (Tm.nlet g e b)])
  (nletrec [n Nat] [g Nat] [fb Tm] [b Tm] [hfb (WS n fb)] [hb (WS n b)] :where [n (Tm.nletrec g fb b)])
  (nfix [n Nat] [g Nat] [fb Tm] [hfb (WS n fb)] :where [n (Tm.nfix g fb)])
  (nhandle [n Nat] [g Nat] [ops (List Nat)] [b Tm] [r Tm] [o Tm] [hb (WS n b)] [hr (WS n r)] [ho (WS n o)]
           :where [n (Tm.nhandle g ops b r o)]))

;; ---------------------------------------------------------------------------
;; Weakening

(a/theorem ws-weaken [n :- Nat, t :- Tm, h :- (WS n t)]
  (forall [m :- Nat] (=> (<= n m) (WS m t)))
  (induction h)
  (all_goals (intro m) (intro hm))
  (all_goals (constructor))
  (all_goals (try (omega)))
  (all_goals (first (apply ih_hb) (apply ih_hf) (apply ih_hx) (apply ih_he) (apply ih_hc) (apply ih_hu)
                    (apply ih_hfb) (apply ih_hy) (apply ih_hr) (apply ih_ho)))
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

(a/theorem ws-subst-var [v :- Tm, hv :- (WS 0 v), i :- Nat, n :- Nat, j :- Nat,
                         h :- (WS (+ n 1) (Tm.var i)), hj :- (<= j n)]
  (WS n (subst j v (Tm.var i)))
  (simp [subst])
  (exact (ws-substVar v hv i n j (ws-var-inv (+ n 1) i h) hj)))

(a/theorem ws-subst-all [v :- Tm, hv :- (WS 0 v), t :- Tm]
  (forall [n :- Nat] (forall [j :- Nat] (=> (WS (+ n 1) t) (=> (<= j n) (WS n (subst j v t))))))
  (induction t)
  (all_goals (intro n) (intro j) (intro h) (intro hj))
  (all_goals (try (apply ws-subst-var) (assumption) (assumption) (assumption)))
  (all_goals (cases h))
  (all_goals (simp [subst]))
  (all_goals (try (constructor)))
  (all_goals (try (first (apply ih_b) (apply ih_f) (apply ih_x) (apply ih_e) (apply ih_c) (apply ih_t)
                         (apply ih_fb) (apply ih_y) (apply ih_r) (apply ih_o) (apply ih_u))))
  (all_goals (try (first (assumption) (omega)))))

(a/theorem ws-subst [n :- Nat, j :- Nat, v :- Tm, t :- Tm,
                     hv :- (WS 0 v), ht :- (WS (+ n 1) t), hj :- (<= j n)]
  (WS n (subst j v t))
  (exact (ws-subst-all v hv t n j ht hj)))

;; ---------------------------------------------------------------------------
;; Pinning does not change scoping (L1.context.get).

(a/theorem ws-pinTm [wi :- Nat, t :- Tm]
  (forall [n :- Nat] (=> (WS n t) (WS n (pinTm wi t))))
  (induction t)
  (all_goals (intro n) (intro h))
  (all_goals (cases h))
  (all_goals (simp [pinTm]))
  (all_goals (constructor))
  (all_goals (try (first (apply ih_b) (apply ih_f) (apply ih_x) (apply ih_e) (apply ih_c) (apply ih_t)
                         (apply ih_fb) (apply ih_y) (apply ih_r) (apply ih_o) (apply ih_u))))
  (all_goals (try (assumption))))

;; ---------------------------------------------------------------------------
;; The closedness check of run is sound (L2.run.closed).

(a/theorem wsb-WS [t :- Tm]
  (forall [m :- Nat] (=> (= Bool (wsb m t) true) (WS m t)))
  (induction t)
  (all_goals (intro m) (intro h))
  (all_goals (simp [wsb] at h))
  (all_goals (constructor))
  (all_goals (try (first (and_then (apply ih_b) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_f) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_x) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_e) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_c) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_t) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_fb) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_y) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_r) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_o) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))) (and_then (apply ih_u) (first (assumption) (exact (And.left h)) (exact (And.right h)) (exact (And.left (And.right h))) (exact (And.right (And.right h))))))))
  (all_goals (try (first (assumption) (omega)))))
