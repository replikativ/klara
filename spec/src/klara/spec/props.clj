(ns klara.spec.props
  "Metatheory of the step function: determinism, preservation of
  well-scopedness, progress modulo named stuck states, and the s-m-n law."
  (:require [ansatz.core :as a]
            [klara.spec.core]
            [klara.spec.ws]))

;; ---------------------------------------------------------------------------
;; The relation Step: the graph of `step`.

(a/inductive Step [] :in Prop :indices [c Config c2 Config]
  (mk [c Config] [c2 Config] [h (= (Option Config) (step c) (Option.some Config c2))] :where [c c2]))

;; Well-scoped worlds and configurations.
(a/inductive WSW [] :in Prop :indices [w World]
  (empty :where [World.empty])
  (bind [id Nat] [v Tm] [rest World] [hv (WS 0 v)] [hr (WSW rest)] :where [(World.bind id v rest)]))

;; Needs ansatz >= 55f52be (Prop elimination follows elim_only_at_universe_zero).
(a/inductive WSC [] :in Prop :indices [c Config]
  (mk [w World] [n Nat] [t Tm] [hw (WSW w)] [ht (WS 0 t)] :where [(Config.mk w n t)]))

;; Outcome invariant: a step stays closed, an effect carries a closed argument
;; and a context closed but for its hole, and a stuck state is a named one.
(a/inductive OK [] :in Prop :indices [o Out]
  (val :where [Out.val])
  (next [n Nat] [e Tm] [he (WS 0 e)] :where [(Out.next n e)])
  (eff [tg (Option Nat)] [op Nat] [v Tm] [k Tm] [hv (WS 0 v)] [hk (WS 1 k)] :where [(Out.eff tg op v k)])
  (stuck [s Stuck] [hs (Not (= Stuck s Stuck.scope))] :where [(Out.stuck s)])
  (chk [ns (List Nat)] [n Nat] [e Tm] [he (WS 0 e)] :where [(Out.chk ns n e)]))

;; ---------------------------------------------------------------------------
;; (a) Determinism: Step is the graph of a function.

(a/theorem step-det [c :- Config, c1 :- Config, c2 :- Config, h1 :- (Step c c1), h2 :- (Step c c2)]
  (= c1 c2)
  (cases h1 :with [(mk x y ha) (cases h2 :with [(mk x2 y2 hb) (rw [ha] at hb) (cases hb) (rfl)])]))

;; ---------------------------------------------------------------------------
;; The outcome invariant, piece by piece.

(a/theorem lookup-ws [w :- World, hw :- (WSW w)]
  (forall [id :- Nat] (forall [v :- Tm] (=> (= (Option Tm) (lookup w id) (Option.some Tm v)) (WS 0 v))))
  (induction hw)
  (all_goals (intro query) (intro answer) (intro h))
  (try (simp only [lookup] at h))
  (cases h)
  (revert h)
  (simp only [lookup])
  (split)
  (all_goals (dsimp) (intro h2))
  (all_goals
    (first (and_then (cases h2) (assumption))
           (exact (ih_hr query answer h2)))))

(a/theorem frame-ok [o :- Out, fr :- (=> Tm Tm), ho :- (OK o),
                     h0 :- (forall [e :- Tm] (=> (WS 0 e) (WS 0 (fr e)))),
                     h1 :- (forall [e :- Tm] (=> (WS 1 e) (WS 1 (fr e))))]
  (OK (frame o fr))
  (cases ho)
  (all_goals (simp [frame]))
  (all_goals (constructor))
  (all_goals (try (first (apply h0) (apply h1))))
  (all_goals (assumption)))

(a/theorem seq1-ok [o :- Out, fr :- (=> Tm Tm), done :- Out, ho :- (OK o), hd :- (OK done),
                    h0 :- (forall [e :- Tm] (=> (WS 0 e) (WS 0 (fr e)))),
                    h1 :- (forall [e :- Tm] (=> (WS 1 e) (WS 1 (fr e))))]
  (OK (seq1 o fr done))
  (cases ho)
  (all_goals (try (simp [seq1, frame])))
  (all_goals (try (assumption)))
  (all_goals (constructor))
  (all_goals (try (first (apply h0) (apply h1))))
  (all_goals (assumption)))

(a/theorem seq2-ok [o1 :- Out, o2 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), done :- Out,
                    ho1 :- (OK o1), ho2 :- (OK o2), hd :- (OK done),
                    h10 :- (forall [e :- Tm] (=> (WS 0 e) (WS 0 (fr1 e)))),
                    h11 :- (forall [e :- Tm] (=> (WS 1 e) (WS 1 (fr1 e)))),
                    h20 :- (forall [e :- Tm] (=> (WS 0 e) (WS 0 (fr2 e)))),
                    h21 :- (forall [e :- Tm] (=> (WS 1 e) (WS 1 (fr2 e))))]
  (OK (seq2 o1 o2 fr1 fr2 done))
  (cases ho1)
  (all_goals (try (simp [seq2, frame])))
  (cases ho2)
  (all_goals (try (simp [frame])))
  (all_goals (try (assumption)))
  (all_goals (constructor))
  (all_goals (try (first (apply h10) (apply h11) (apply h20) (apply h21))))
  (all_goals (assumption)))

(a/theorem beta-ok [n :- Nat, f :- Tm, x :- Tm, hf :- (WS 0 f), hx :- (WS 0 x)]
  (OK (beta n f x))
  (cases hf)
  (all_goals (try (omega)))
  (all_goals (simp [beta]))
  (all_goals (constructor))
  (all_goals (try (intro hh) (cases hh)))
  (all_goals (apply ws-substF'))
  (all_goals (try (first (assumption) (omega))))
  (apply ws-substF')
  (all_goals (try (first (assumption) (omega) (constructor))))
  (all_goals (try (first (assumption) (omega)))))

(a/theorem primResult-ok [n :- Nat, r :- (Option Datum)] (OK (primResult n r))
  (cases r)
  (all_goals (simp [primResult]))
  (all_goals (constructor))
  (all_goals (try (intro hh) (cases hh)))
  (all_goals (try (constructor))))

(a/theorem primStep-ok [n :- Nat, op :- PrimOp, x :- Tm, y :- Tm]
  (OK (primStep n op x y))
  (cases x)
  (all_goals (try (simp [primStep]) (constructor) (intro hh) (cases hh)))
  (cases y)
  (all_goals (try (simp [primStep]) (constructor) (intro hh) (cases hh)))
  (simp [primStep])
  (apply primResult-ok))

(a/theorem resolveResult-ok [n :- Nat, id :- Nat, r :- (Option Tm),
                             h :- (forall [v :- Tm] (=> (= (Option Tm) r (Option.some Tm v)) (WS 0 v)))]
  (OK (resolveResult n id r))
  (cases r)
  (all_goals (simp [resolveResult]))
  (constructor) (intro hh) (cases hh)
  (constructor) (apply h) (rfl))

(a/theorem performStep-ok [op :- Nat, h :- Tm, x :- Tm, hx :- (WS 0 x)]
  (OK (performStep op h x))
  (cases h)
  (all_goals (try (simp [performStep]) (constructor) (intro hh) (cases hh)))
  (cases d)
  (all_goals (simp [performStep]))
  (all_goals (constructor))
  (all_goals (try (intro hh) (cases hh)))
  (all_goals (try (assumption)))
  (all_goals (constructor))
  (all_goals (omega)))

(a/theorem handleEff-ok [n :- Nat, l :- Nat, r :- Tm, o :- Tm, tg :- (Option Nat), op :- Nat, v :- Tm, k :- Tm,
                         hr :- (WS 1 r), ho :- (WS 3 o), hv :- (WS 0 v), hk :- (WS 1 k)]
  (OK (handleEff n l r o tg op v k))
  (have hr2 (WS 2 r)) (apply (ws-weaken 1 r hr)) (omega)
  (have ho4 (WS 4 o)) (apply (ws-weaken 3 o ho)) (omega)
  (have hh (WS 1 (Tm.handling l k r o))) (constructor) (assumption) (assumption) (assumption)
  (have hl (WS 0 (Tm.lam (Tm.handling l k r o)))) (constructor) (assumption)
  (have h2 (WS 2 (substF (Tm.lam (Tm.handling l k r o)) o 0))) (apply ws-substF') (assumption) (assumption) (omega)
  (have h1 (WS 1 (substF v (substF (Tm.lam (Tm.handling l k r o)) o 0) 0))) (apply ws-substF') (assumption) (assumption) (omega)
  (cases tg)
  (all_goals (simp [handleEff]))
  (constructor) (assumption) (assumption)
  (split_ifs)
  (all_goals (try (dsimp)))
  (all_goals (constructor))
  (all_goals (try (assumption)))
  (apply ws-substF') (constructor) (assumption) (omega))

(a/theorem handlingOut-ok [n :- Nat, l :- Nat, b :- Tm, r :- Tm, o :- Tm, ob :- Out,
                           hb :- (WS 0 b), hr :- (WS 1 r), ho :- (WS 3 o), hob :- (OK ob)]
  (OK (handlingOut n l b r o ob))
  (cases hob)
  (all_goals (simp [handlingOut]))
  ;; val: the return clause
  (constructor) (apply ws-substF') (assumption) (assumption) (omega)
  ;; next: step under the handling frame
  (constructor) (constructor) (assumption) (assumption) (assumption)
  ;; eff: the handler rule
  (apply handleEff-ok) (assumption) (assumption) (assumption) (assumption)
  ;; stuck
  (constructor) (assumption)
  ;; chk: a splice under the handling frame
  (constructor) (constructor) (assumption) (assumption) (assumption))

(a/theorem ws-1-2 [t :- Tm, h :- (WS 1 t)] (WS 2 t)
  (apply (ws-weaken 1 t h)) (omega))

;; ---------------------------------------------------------------------------
;; Staging pieces of the outcome invariant (S5).

(a/theorem seq3-ok [o1 :- Out, o2 :- Out, o3 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), fr3 :- (=> Tm Tm),
                    done :- Out, ho1 :- (OK o1), ho2 :- (OK o2), ho3 :- (OK o3), hd :- (OK done),
                    h10 :- (forall [e :- Tm] (=> (WS 0 e) (WS 0 (fr1 e)))),
                    h11 :- (forall [e :- Tm] (=> (WS 1 e) (WS 1 (fr1 e)))),
                    h20 :- (forall [e :- Tm] (=> (WS 0 e) (WS 0 (fr2 e)))),
                    h21 :- (forall [e :- Tm] (=> (WS 1 e) (WS 1 (fr2 e)))),
                    h30 :- (forall [e :- Tm] (=> (WS 0 e) (WS 0 (fr3 e)))),
                    h31 :- (forall [e :- Tm] (=> (WS 1 e) (WS 1 (fr3 e))))]
  (OK (seq3 o1 o2 o3 fr1 fr2 fr3 done))
  (cases ho1)
  (all_goals (try (simp [seq3, frame])))
  (exact (seq2-ok o2 o3 fr2 fr3 done ho2 ho3 hd h20 h21 h30 h31))

  (all_goals (constructor))
  (all_goals (try (first (apply h10) (apply h11))))
  (all_goals (assumption)))

(a/theorem atZero-ok [l :- Nat, x :- Out, y :- Out, hx :- (OK x), hy :- (OK y)] (OK (atZero l x y))
  (cases l) (all_goals (simp only [atZero])) (all_goals (assumption)))

(a/theorem dropOut-ok [g :- Nat, k :- Nat, o :- Out, ho :- (OK o)] (OK (dropOut g k o))
  (cases ho) (all_goals (simp only [dropOut])) (all_goals (constructor)) (all_goals (assumption)))

(a/theorem stuck-stage-ok [] (OK (Out.stuck Stuck.stage))
  (apply OK.stuck) (intro hh) (cases hh))

(a/theorem stuck-lift-ok [] (OK (Out.stuck Stuck.lift))
  (apply OK.stuck) (intro hh) (cases hh))

(a/theorem stuck-extrusion-ok [] (OK (Out.stuck Stuck.extrusion))
  (apply OK.stuck) (intro hh) (cases hh))

(a/theorem openLam-ok [n :- Nat, b :- Tm, hb :- (WS 1 b)] (OK (openLam n b))
  (simp only [openLam]) (constructor) (constructor)
  (apply ws-subst) (constructor) (assumption) (omega))

(a/theorem openLet-ok [n :- Nat, e :- Tm, b :- Tm, he :- (WS 0 e), hb :- (WS 1 b)] (OK (openLet n e b))
  (simp only [openLet]) (constructor) (constructor) (assumption)
  (apply ws-subst) (constructor) (assumption) (omega))

(a/theorem openLetrec-ok [n :- Nat, fb :- Tm, b :- Tm, hfb :- (WS 2 fb), hb :- (WS 1 b)] (OK (openLetrec n fb b))
  (simp only [openLetrec]) (constructor) (constructor)
  (apply ws-subst) (constructor) (apply ws-subst) (constructor) (assumption) (omega) (omega)
  (apply ws-subst) (constructor) (assumption) (omega))

(a/theorem openHandle-ok [n :- Nat, b :- Tm, r :- Tm, o :- Tm, hb :- (WS 1 b), hr :- (WS 1 r), ho :- (WS 3 o)]
  (OK (openHandle n b r o))
  (simp only [openHandle]) (constructor) (constructor)
  (apply ws-subst) (constructor) (assumption) (omega)
  (apply ws-subst) (constructor) (assumption) (omega)
  (apply ws-subst) (constructor) (apply ws-subst) (constructor) (apply ws-subst) (constructor) (assumption)
  (omega) (omega) (omega))

(a/theorem splice-ok [n :- Nat, u :- Tm, hu :- (WS 0 u)] (OK (splice n u))
  (cases hu)
  (all_goals (simp only [splice]))
  (all_goals (try (apply stuck-stage-ok)))
  (constructor) (assumption))

(a/theorem escAt-ok [m :- Nat, n :- Nat, u :- Tm, o :- Out, hu :- (WS 0 u), ho :- (OK o)] (OK (escAt m n u o))
  (cases m)
  (all_goals (simp only [escAt]))
  (apply seq1-ok) (assumption) (apply splice-ok) (assumption)
  (all_goals (try (apply frame-ok) (assumption)))
  (all_goals (intro e) (intro he) (constructor) (assumption)))

(a/theorem escOut-ok [l :- Nat, n :- Nat, u :- Tm, o :- Out, hu :- (WS 0 u), ho :- (OK o)] (OK (escOut l n u o))
  (cases l)
  (all_goals (simp only [escOut]))
  (apply stuck-stage-ok)
  (apply escAt-ok) (assumption) (assumption))

(a/theorem runCode-ok [n :- Nat, c :- Tm] (OK (runCode n c))
  (cases heq (wsbF c 0))
  (all_goals (simp only [runCode, heq]))
  (apply stuck-extrusion-ok)
  (constructor) (exact (wsbF-WS c 0 heq)))

(a/theorem runStep-ok [n :- Nat, u :- Tm] (OK (runStep n u))
  (cases u)
  (all_goals (simp only [runStep]))
  (all_goals (try (apply stuck-stage-ok)))
  (apply runCode-ok))

(a/theorem pick-ws [c :- Tm, u :- Tm, e :- Tm, hu :- (WS 0 u), he :- (WS 0 e)] (WS 0 (pick c u e))
  (simp only [pick]) (split) (all_goals (assumption)))

;; Frames: closed stays closed, closed-but-hole stays closed-but-hole.
;; One lemma per constructor: the main induction (ev-ok) then only dispatches.

(a/theorem ev-lam-ok [w :- World, n :- Nat, b :- Tm, l :- Nat, hb :- (WS 1 b)]
  (OK (ev w n (Tm.lam b) l))
  (simp only [ev]) (apply atZero-ok) (constructor) (apply openLam-ok) (assumption))

(a/theorem ev-app-ok [w :- World, n :- Nat, f :- Tm, x :- Tm, l :- Nat, hf :- (WS 0 f), hx :- (WS 0 x),
                      of :- (OK (ev w n f l)), ox :- (OK (ev w n x l))]
  (OK (ev w n (Tm.app f x) l))
  (simp only [ev])
  (apply seq2-ok) (exact of) (exact ox)
  (apply atZero-ok) (apply beta-ok) (assumption) (assumption) (constructor)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-let-ok [w :- World, n :- Nat, e :- Tm, b :- Tm, l :- Nat, he :- (WS 0 e), hb :- (WS 1 b),
                      oe :- (OK (ev w n e l))]
  (OK (ev w n (Tm.let_ e b) l))
  (simp only [ev])
  (apply atZero-ok)
  (apply seq1-ok) (exact oe)
  (constructor) (apply ws-subst) (assumption) (assumption) (omega)
  (intro e2) (intro he2) (try (dsimp)) (constructor) (assumption) (assumption)
  (intro e2) (intro he2) (try (dsimp)) (constructor) (assumption) (apply ws-1-2) (assumption)
  (apply openLet-ok) (assumption) (assumption))

(a/theorem ev-if-ok [w :- World, n :- Nat, c :- Tm, u :- Tm, e :- Tm, l :- Nat,
                     hc :- (WS 0 c), hu :- (WS 0 u), he :- (WS 0 e),
                     oc :- (OK (ev w n c l)), ou :- (OK (ev w n u l)), oe :- (OK (ev w n e l))]
  (OK (ev w n (Tm.if_ c u e) l))
  (simp only [ev])
  (apply atZero-ok)
  (apply seq1-ok) (exact oc)
  (constructor) (apply pick-ws) (assumption) (assumption)
  (intro e2) (intro he2) (try (dsimp)) (constructor) (assumption) (assumption) (assumption)
  (intro e2) (intro he2) (try (dsimp)) (constructor) (assumption)
  (apply ws-closed) (assumption) (apply ws-closed) (assumption)
  (apply seq3-ok) (exact oc) (exact ou) (exact oe) (constructor)
  (all_goals (intro e2) (intro he2) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-letrec-ok [w :- World, n :- Nat, fb :- Tm, b :- Tm, l :- Nat, hfb :- (WS 2 fb), hb :- (WS 1 b)]
  (OK (ev w n (Tm.letrec fb b) l))
  (simp only [ev]) (apply atZero-ok)
  (constructor) (apply ws-subst) (constructor) (assumption) (assumption) (omega)
  (apply openLetrec-ok) (assumption) (assumption))

(a/theorem ev-resolve-ok [w :- World, hw :- (WSW w), n :- Nat, id :- Nat, l :- Nat]
  (OK (ev w n (Tm.resolve id) l))
  (simp only [ev]) (apply atZero-ok)
  (apply resolveResult-ok) (intro v0) (intro hl) (exact (lookup-ws w hw _ _ hl))
  (constructor))

(a/theorem ev-prim-ok [w :- World, n :- Nat, op :- PrimOp, x :- Tm, y :- Tm, l :- Nat, hx :- (WS 0 x), hy :- (WS 0 y),
                       ox :- (OK (ev w n x l)), oy :- (OK (ev w n y l))]
  (OK (ev w n (Tm.prim op x y) l))
  (simp only [ev])
  (apply seq2-ok) (exact ox) (exact oy)
  (apply atZero-ok) (apply primStep-ok) (constructor)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-perform-ok [w :- World, n :- Nat, op :- Nat, h :- Tm, x :- Tm, l :- Nat, hh :- (WS 0 h), hx :- (WS 0 x),
                          oh :- (OK (ev w n h l)), ox :- (OK (ev w n x l))]
  (OK (ev w n (Tm.perform op h x) l))
  (simp only [ev])
  (apply seq2-ok) (exact oh) (exact ox)
  (apply atZero-ok) (apply performStep-ok) (assumption) (constructor)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-handle-ok [w :- World, n :- Nat, b :- Tm, r :- Tm, o :- Tm, l :- Nat,
                         hb :- (WS 1 b), hr :- (WS 1 r), ho :- (WS 3 o)]
  (OK (ev w n (Tm.handle b r o) l))
  (simp only [ev]) (apply atZero-ok)
  (constructor) (constructor) (apply ws-subst) (constructor) (assumption) (omega) (assumption) (assumption)
  (apply openHandle-ok) (assumption) (assumption) (assumption))

(a/theorem ev-specialize-ok [w :- World, n :- Nat, p :- Tm, m :- Tm, l :- Nat, hp :- (WS 0 p), hm :- (WS 0 m),
                             op :- (OK (ev w n p l)), om :- (OK (ev w n m l))]
  (OK (ev w n (Tm.specialize p m) l))
  (simp only [ev])
  (apply seq2-ok) (exact op) (exact om)
  (apply atZero-ok)
  (constructor) (constructor) (constructor) (constructor)
  (apply ws-closed) (assumption) (apply ws-closed) (assumption) (constructor) (omega)
  (constructor)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-cap-ok [w :- World, n :- Nat, c :- Nat, l :- Nat] (OK (ev w n (Tm.cap c) l))
  (simp only [ev]) (apply atZero-ok) (constructor) (apply stuck-lift-ok))

(a/theorem ev-handling-ok [w :- World, n :- Nat, c :- Nat, b :- Tm, r :- Tm, o :- Tm, l :- Nat,
                           hb :- (WS 0 b), hr :- (WS 1 r), ho :- (WS 3 o), ob :- (OK (ev w n b l))]
  (OK (ev w n (Tm.handling c b r o) l))
  (simp only [ev]) (apply atZero-ok)
  (apply handlingOut-ok) (assumption) (assumption) (assumption) (exact ob)
  (apply stuck-lift-ok))

(a/theorem ev-code-ok [w :- World, n :- Nat, u :- Tm, l :- Nat, hu :- (WS 0 u), ou :- (OK (ev w n u (+ l 1)))]
  (OK (ev w n (Tm.code u) l))
  (simp only [ev]) (apply frame-ok) (exact ou)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-esc-ok [w :- World, n :- Nat, u :- Tm, l :- Nat, hu :- (WS 0 u), ou :- (OK (ev w n u (- l 1)))]
  (OK (ev w n (Tm.esc u) l))
  (simp only [ev]) (apply escOut-ok) (assumption) (exact ou))

(a/theorem ev-run-ok [w :- World, n :- Nat, u :- Tm, l :- Nat, hu :- (WS 0 u), ou :- (OK (ev w n u l))]
  (OK (ev w n (Tm.run_ u) l))
  (simp only [ev]) (apply atZero-ok)
  (apply seq1-ok) (exact ou) (apply runStep-ok)
  (intro e) (intro he) (try (dsimp)) (constructor) (assumption)
  (intro e) (intro he) (try (dsimp)) (constructor) (assumption)
  (apply frame-ok) (exact ou)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-gvar-ok [w :- World, n :- Nat, g :- Nat, l :- Nat] (OK (ev w n (Tm.gvar g) l))
  (simp only [ev]) (apply atZero-ok) (constructor) (constructor) (constructor) (constructor))

(a/theorem ev-nlam-ok [w :- World, n :- Nat, g :- Nat, b :- Tm, l :- Nat, hb :- (WS 0 b), ob :- (OK (ev w n b l))]
  (OK (ev w n (Tm.nlam g b) l))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply dropOut-ok) (apply frame-ok) (exact ob)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-nlet-ok [w :- World, n :- Nat, g :- Nat, e :- Tm, b :- Tm, l :- Nat, he :- (WS 0 e), hb :- (WS 0 b),
                       oe :- (OK (ev w n e l)), ob :- (OK (ev w n b l))]
  (OK (ev w n (Tm.nlet g e b) l))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply dropOut-ok) (apply seq2-ok) (exact oe) (exact ob) (constructor)
  (all_goals (intro e2) (intro he2) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-nletrec-ok [w :- World, n :- Nat, g :- Nat, fb :- Tm, b :- Tm, l :- Nat, hfb :- (WS 0 fb), hb :- (WS 0 b),
                          ofb :- (OK (ev w n fb l)), ob :- (OK (ev w n b l))]
  (OK (ev w n (Tm.nletrec g fb b) l))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply dropOut-ok) (apply seq2-ok) (exact ofb) (exact ob) (constructor)
  (all_goals (intro e2) (intro he2) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-nhandle-ok [w :- World, n :- Nat, g :- Nat, b :- Tm, r :- Tm, o :- Tm, l :- Nat,
                          hb :- (WS 0 b), hr :- (WS 0 r), ho :- (WS 0 o),
                          ob :- (OK (ev w n b l)), or :- (OK (ev w n r l)), oo :- (OK (ev w n o l))]
  (OK (ev w n (Tm.nhandle g b r o) l))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply dropOut-ok) (apply seq3-ok) (exact oo) (exact or) (exact ob) (constructor)
  (all_goals (intro e2) (intro he2) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

;; The outcome of a closed term at any level in a closed world satisfies the
;; invariant. This one induction carries both preservation and progress:
;; every `next` and `chk` is closed, and no stuck state is the unnamed `scope`.
;; ansatz-specific: the goals are discharged in constructor order; a
;; `first` over the case lemmas makes `apply` unfold `ev` on every mismatch
;; and does not finish in 15 minutes (see README).
(a/theorem ev-ok [w :- World, hw :- (WSW w), n :- Nat, t :- Tm]
  (forall [l :- Nat] (=> (WS 0 t) (OK (ev w n t l))))
  (induction t)
  (all_goals (intro l) (intro ht))
  (all_goals (cases ht))
  ;; var
  (omega)
  ;; lit
  (simp only [ev]) (constructor)
  ;; lam
  (apply ev-lam-ok) (assumption)
  ;; app
  (apply ev-app-ok) (assumption) (assumption) (apply ih_f) (assumption) (apply ih_x) (assumption)
  ;; let_
  (apply ev-let-ok) (assumption) (assumption) (apply ih_e) (assumption)
  ;; if_
  (apply ev-if-ok) (assumption) (assumption) (assumption) (apply ih_c) (assumption) (apply ih_t) (assumption)
  (apply ih_e) (assumption)
  ;; letrec
  (apply ev-letrec-ok) (assumption) (assumption)
  ;; resolve
  (apply ev-resolve-ok) (assumption)
  ;; prim
  (apply ev-prim-ok) (assumption) (assumption) (apply ih_x) (assumption) (apply ih_y) (assumption)
  ;; perform
  (apply ev-perform-ok) (assumption) (assumption) (apply ih_h) (assumption) (apply ih_x) (assumption)
  ;; handle
  (apply ev-handle-ok) (assumption) (assumption) (assumption)
  ;; specialize
  (apply ev-specialize-ok) (assumption) (assumption) (apply ih_p) (assumption) (apply ih_m) (assumption)
  ;; fix
  (simp only [ev]) (constructor)
  ;; cap
  (apply ev-cap-ok)
  ;; handling
  (apply ev-handling-ok) (assumption) (assumption) (assumption) (apply ih_b) (assumption)
  ;; code, esc, run_
  (apply ev-code-ok) (assumption) (apply ih_t) (assumption)
  (apply ev-esc-ok) (assumption) (apply ih_t) (assumption)
  (apply ev-run-ok) (assumption) (apply ih_t) (assumption)
  ;; gvar
  (apply ev-gvar-ok)
  ;; n-forms
  (apply ev-nlam-ok) (assumption) (apply ih_b) (assumption)
  (apply ev-nlet-ok) (assumption) (assumption) (apply ih_e) (assumption) (apply ih_b) (assumption)
  (apply ev-nletrec-ok) (assumption) (assumption) (apply ih_fb) (assumption) (apply ih_b) (assumption)
  (apply ev-nhandle-ok) (assumption) (assumption) (assumption) (apply ih_b) (assumption) (apply ih_r) (assumption)
  (apply ih_o) (assumption))

(a/theorem run1-ok [w :- World, hw :- (WSW w), n :- Nat, t :- Tm]
  (=> (WS 0 t) (OK (run1 w n t)))
  (intro ht) (simp only [run1]) (exact (ev-ok w hw n t 0 ht)))

(a/theorem stepOut-ok [w :- World, o :- Out, w2 :- World, n2 :- Nat, t2 :- Tm,
                       ho :- (OK o), hw :- (WSW w),
                       h :- (= (Option Config) (stepOut w o) (Option.some Config (Config.mk w2 n2 t2)))]
  (And (WSW w2) (WS 0 t2))
  (cases ho)
  (all_goals (simp only [stepOut] at h))
  ;; val, next, eff, stuck
  (cases h)
  (cases h) (constructor) (assumption) (assumption)
  (cases h)
  (cases h)
  ;; chk: steps only when every spliced name is alive
  ;; ansatz-specific: `cases h` on an equation whose left side is the
  ;; unreduced `chkStep ..` yields a kernel-rejected proof (see README), so
  ;; the list is split first.
  (revert h) (cases ns)
  (intro h) (simp only [chkStep] at h) (cases h) (constructor) (assumption) (assumption)
  (intro h) (simp only [chkStep] at h) (cases h))

;; ---------------------------------------------------------------------------
;; (c) Preservation of well-scopedness.

(a/theorem preservation [w :- World, n :- Nat, t :- Tm, w2 :- World, n2 :- Nat, t2 :- Tm,
                         hs :- (Step (Config.mk w n t) (Config.mk w2 n2 t2)),
                         hw :- (WSW w), ht :- (WS 0 t)]
  (And (WSW w2) (WS 0 t2))
  (cases hs)
  (simp [step] at h)
  (exact (stepOut-ok w (run1 w n t) w2 n2 t2 (run1-ok w hw n t ht) hw h)))

;; Simple values (lit, lam, fix, cap) are values at level 0. Code values
;; `code u` are values too but not `isVal`: their valuehood is recursive
;; (u fully built at level 1); Progress states `value` as run1 = val.
(a/theorem isVal-run1 [w :- World, n :- Nat, t :- Tm, h :- (= Bool (isVal t) Bool.true)]
  (= Out (run1 w n t) Out.val)
  (cases t)
  (all_goals (try (simp [isVal] at h)))
  (all_goals (simp [run1, ev, atZero])))

;; ---------------------------------------------------------------------------
;; (b) Progress modulo named stuck states.
;;
;; A closed configuration is a value, steps, is an effect no handler instance
;; in its context catches (an ambient op at top level, or a capability that
;; escaped its instance), or is a named error. The unnamed failure `scope`
;; is excluded.

(a/inductive Progress [] :in Prop :indices [c Config]
  (value [w World] [n Nat] [t Tm] [h (= Out (run1 w n t) Out.val)] :where [(Config.mk w n t)])
  (steps [c Config] [c2 Config] [h (Step c c2)] :where [c])
  (unhandled [w World] [n Nat] [t Tm] [tg (Option Nat)] [op Nat] [v Tm] [k Tm]
             [h (= Out (run1 w n t) (Out.eff tg op v k))] :where [(Config.mk w n t)])
  (error [w World] [n Nat] [t Tm] [s Stuck] [h (= Out (run1 w n t) (Out.stuck s))]
         [hs (Not (= Stuck s Stuck.scope))] :where [(Config.mk w n t)])
  ;; a splice of code that mentions a generated name whose binder is not on
  ;; the path to the redex (scope extrusion, BER MetaOCaml's dynamic check)
  (extrusion [w World] [n Nat] [t Tm] [g Nat] [gs (List Nat)] [n2 Nat] [e Tm]
             [h (= Out (run1 w n t) (Out.chk (List.cons Nat g gs) n2 e))] :where [(Config.mk w n t)]))

(a/theorem progress-next [w :- World, n :- Nat, t :- Tm, n2 :- Nat, e2 :- Tm]
  (=> (= Out (run1 w n t) (Out.next n2 e2)) (Progress (Config.mk w n t)))
  (intro hq)
  (have hs (= (Option Config) (step (Config.mk w n t)) (Option.some Config (Config.mk w n2 e2))))
  (simp [step, hq, stepOut])
  (exact (Progress.steps (Config.mk w n t) (Config.mk w n2 e2)
           (Step.mk (Config.mk w n t) (Config.mk w n2 e2) hs))))

(a/theorem progress-eff [w :- World, n :- Nat, t :- Tm, tg :- (Option Nat), op :- Nat, v :- Tm, k :- Tm]
  (=> (= Out (run1 w n t) (Out.eff tg op v k)) (Progress (Config.mk w n t)))
  (intro hq) (exact (Progress.unhandled w n t tg op v k hq)))

(a/theorem progress-stuck [w :- World, n :- Nat, t :- Tm, s :- Stuck, hs :- (Not (= Stuck s Stuck.scope))]
  (=> (= Out (run1 w n t) (Out.stuck s)) (Progress (Config.mk w n t)))
  (intro hq) (exact (Progress.error w n t s hq hs)))

(a/theorem progress-val [w :- World, n :- Nat, t :- Tm]
  (=> (= Out (run1 w n t) Out.val) (Progress (Config.mk w n t)))
  (intro hq) (exact (Progress.value w n t hq)))

(a/theorem progress-chk [w :- World, n :- Nat, t :- Tm, ns :- (List Nat), n2 :- Nat, e2 :- Tm]
  (=> (= Out (run1 w n t) (Out.chk ns n2 e2)) (Progress (Config.mk w n t)))
  (intro hq)
  (cases ns)
  (have hs (= (Option Config) (step (Config.mk w n t)) (Option.some Config (Config.mk w n2 e2))))
  (simp [step, hq, stepOut, chkStep])
  (exact (Progress.steps (Config.mk w n t) (Config.mk w n2 e2)
           (Step.mk (Config.mk w n t) (Config.mk w n2 e2) hs)))
  (exact (Progress.extrusion w n t head tail n2 e2 hq)))

(a/theorem progress [w :- World, n :- Nat, t :- Tm, hw :- (WSW w), ht :- (WS 0 t)]
  (Progress (Config.mk w n t))
  (have hok (OK (run1 w n t))) (exact (run1-ok w hw n t ht))
  (cases heq (run1 w n t))
  (revert heq) (apply progress-val)
  (revert heq) (apply progress-next)
  (revert heq) (apply progress-eff)
  (have hs (Not (= Stuck s Stuck.scope))) (rw [heq] at hok) (cases hok) (assumption)
  (revert heq) (apply progress-stuck) (assumption)
  (revert heq) (apply progress-chk))

;; ---------------------------------------------------------------------------
;; (d) The s-m-n law for the trivial specializer, as step equivalence.

(a/inductive Star [] :in Prop :indices [c Config c2 Config]
  (refl [c Config] :where [c c])
  (step [c Config] [c2 Config] [c3 Config] [h (Step c c2)] [hs (Star c2 c3)] :where [c c3]))

;; By determinism, a run that reaches a terminal configuration passes through
;; every successor.
(a/theorem star-det [c :- Config, c1 :- Config, c3 :- Config, hs :- (Star c c3),
                     ht :- (forall [d :- Config] (Not (Step c3 d))), h1 :- (Step c c1)]
  (Star c1 c3)
  (cases hs :with
    [(refl x) (exfalso) (exact (ht c1 h1))]
    [(step x y z hxy hyz) (have he (= Config c1 y)) (exact (step-det x c1 y h1 hxy)) (rw [he]) (exact hyz)]))

;; (specialize p m) steps to (fn [y] (p m y)) ...
(a/theorem smn-step1 [w :- World, n :- Nat, p :- Tm, m :- Tm, x :- Tm,
                      vp :- (= Bool (isVal p) Bool.true), vm :- (= Bool (isVal m) Bool.true),
                      vx :- (= Bool (isVal x) Bool.true)]
  (Step (Config.mk w n (Tm.app (Tm.specialize p m) x))
        (Config.mk w n (Tm.app (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0))) x)))
  (have rp (= Out (ev w n p 0) Out.val)) (exact (isVal-run1 w n p vp))
  (have rm (= Out (ev w n m 0) Out.val)) (exact (isVal-run1 w n m vm))
  (have rx (= Out (ev w n x 0) Out.val)) (exact (isVal-run1 w n x vx))
  (have r1 (= (Option Config) (step (Config.mk w n (Tm.app (Tm.specialize p m) x)))
              (Option.some Config (Config.mk w n (Tm.app (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0))) x)))))
  (simp only [step, run1, ev]) (rw [rp, rm, rx])
  (exact (Step.mk _ _ r1)))

;; ... which, applied to a value, beta-reduces to (p m x): p and m are closed.
(a/theorem smn-step2 [w :- World, n :- Nat, p :- Tm, m :- Tm, x :- Tm,
                      hp :- (WS 0 p), hm :- (WS 0 m), vx :- (= Bool (isVal x) Bool.true)]
  (Step (Config.mk w n (Tm.app (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0))) x))
        (Config.mk w n (Tm.app (Tm.app p m) x)))
  (have rx (= Out (ev w n x 0) Out.val)) (exact (isVal-run1 w n x vx))
  (have cp (= Tm (substF x p 0) p)) (exact (substF-closed x p 0 hp))
  (have cm (= Tm (substF x m 0) m)) (exact (substF-closed x m 0 hm))
  (have r2 (= (Option Config) (step (Config.mk w n (Tm.app (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0))) x)))
              (Option.some Config (Config.mk w n (Tm.app (Tm.app p m) x)))))
  ;; ansatz-specific: `simp [ev, ..]` leaves the level abstraction
  ;; `(fun l => ..) 0` unreduced, so the outcome is unfolded by hand and the
  ;; rest closes by rw (which tries rfl).
  (simp only [step, run1]) (simp only [ev]) (rw [rx]) (rw [cp, cm])
  (exact (Step.mk _ _ r2)))

;; s-m-n (MC I eq. 12, trivial specializer): ((specialize p m) x) reduces to (p m x).
(a/theorem smn [w :- World, n :- Nat, p :- Tm, m :- Tm, x :- Tm,
                hp :- (WS 0 p), hm :- (WS 0 m),
                vp :- (= Bool (isVal p) Bool.true), vm :- (= Bool (isVal m) Bool.true),
                vx :- (= Bool (isVal x) Bool.true)]
  (Star (Config.mk w n (Tm.app (Tm.specialize p m) x)) (Config.mk w n (Tm.app (Tm.app p m) x)))
  (exact (Star.step _ _ _ (smn-step1 w n p m x vp vm vx)
           (Star.step _ _ _ (smn-step2 w n p m x hp hm vx) (Star.refl _)))))

;; Step equivalence: both sides reach the same terminal configurations.
(a/theorem smn-equiv [w :- World, n :- Nat, p :- Tm, m :- Tm, x :- Tm, c3 :- Config,
                      hp :- (WS 0 p), hm :- (WS 0 m),
                      vp :- (= Bool (isVal p) Bool.true), vm :- (= Bool (isVal m) Bool.true),
                      vx :- (= Bool (isVal x) Bool.true),
                      ht :- (forall [d :- Config] (Not (Step c3 d))),
                      hs :- (Star (Config.mk w n (Tm.app (Tm.specialize p m) x)) c3)]
  (Star (Config.mk w n (Tm.app (Tm.app p m) x)) c3)
  (exact (star-det _ _ c3 (star-det _ _ c3 hs ht (smn-step1 w n p m x vp vm vx)) ht
           (smn-step2 w n p m x hp hm vx))))

;; ---------------------------------------------------------------------------
;; The headline statements on configurations.

(a/theorem preservation-config [c :- Config, c2 :- Config, hs :- (Step c c2), hc :- (WSC c)]
  (WSC c2)
  (cases hc :with
    [(mk w n t hw ht)
     (cases c2 :with
       [(mk w2 n2 t2)
        (have hp (And (WSW w2) (WS 0 t2))) (exact (preservation w n t w2 n2 t2 hs hw ht))
        (obtain [h1 h2] := hp)
        (exact (WSC.mk w2 n2 t2 h1 h2))])]))

(a/theorem progress-config [c :- Config, hc :- (WSC c)]
  (Progress c)
  (cases hc :with [(mk w n t hw ht) (exact (progress w n t hw ht))]))

;; Type safety: a closed configuration never reaches the unnamed stuck state.
(a/theorem safety [c :- Config, c2 :- Config, hc :- (WSC c), hs :- (Star c c2)]
  (Progress c2)
  (induction hs)
  (all_goals (try (exact (progress-config _ hc))))
  (exact (ih_hs (preservation-config _ _ h hc))))

;; ---------------------------------------------------------------------------
;; (e) run of quoted code: for an escape-free, binder-free term t,
;; (run (code t)) steps to t in one step. Building such a term creates no
;; names, so the code value is t itself, and run's closedness check passes.

(a/inductive Quotable [] :in Prop :indices [t Tm]
  (lit [d Datum] :where [(Tm.lit d)])
  (resolve [id Nat] :where [(Tm.resolve id)])
  (app [f Tm] [x Tm] [hf (Quotable f)] [hx (Quotable x)] :where [(Tm.app f x)])
  (if_ [c Tm] [u Tm] [e Tm] [hc (Quotable c)] [hu (Quotable u)] [he (Quotable e)] :where [(Tm.if_ c u e)])
  (prim [op PrimOp] [x Tm] [y Tm] [hx (Quotable x)] [hy (Quotable y)] :where [(Tm.prim op x y)])
  (perform [op Nat] [h Tm] [x Tm] [hh (Quotable h)] [hx (Quotable x)] :where [(Tm.perform op h x)])
  (specialize [p Tm] [m Tm] [hp (Quotable p)] [hm (Quotable m)] :where [(Tm.specialize p m)]))

(a/theorem quotable-built [w :- World, n :- Nat, t :- Tm, l :- Nat, h :- (Quotable t)]
  (= Out (ev w n t (+ l 1)) Out.val)
  (induction h)
  (all_goals (simp only [ev]))
  (all_goals (try (simp only [atZero])))
  (all_goals (try (rw [ih_hf, ih_hx])))
  (all_goals (try (rw [ih_hc, ih_hu, ih_he])))
  (all_goals (try (rw [ih_hx, ih_hy])))
  (all_goals (try (rw [ih_hh, ih_hx])))
  (all_goals (try (rw [ih_hp, ih_hm])))
  (all_goals (try (rfl))))

(a/theorem quotable-toDB [t :- Tm, h :- (Quotable t)] (= Tm (toDB t) t)
  (induction h)
  (all_goals (simp [toDB]))
  (all_goals (try (simp_all))))

(a/theorem quotable-wsb [t :- Tm, h :- (Quotable t)] (forall [m :- Nat] (= Bool (wsbF t m) true))
  (induction h)
  (all_goals (intro m))
  (all_goals (simp [wsbF]))
  (all_goals (try (simp_all))))

(a/theorem run-quote [w :- World, n :- Nat, t :- Tm, h :- (Quotable t)]
  (Step (Config.mk w n (Tm.run_ (Tm.code t))) (Config.mk w n t))
  (have hb (= Out (ev w n t 1) Out.val)) (exact (quotable-built w n t 0 h))
  (have hd (= Tm (toDB t) t)) (exact (quotable-toDB t h))
  (have hw (= Bool (wsbF t 0) true)) (exact (quotable-wsb t h 0))
  (have r (= (Option Config) (step (Config.mk w n (Tm.run_ (Tm.code t)))) (Option.some Config (Config.mk w n t))))
  (simp only [step, run1]) (try (simp only [ev])) (rw [hb]) (try (rw [hd])) (try (rw [hw])) (try (rfl))
  (exact (Step.mk _ _ r)))
