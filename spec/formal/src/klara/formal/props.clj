(ns klara.formal.props
  "Metatheory of the formal semantics: determinism, preservation of
  well-scopedness, progress modulo named stuck states, and safety (a closed
  program never reaches the unnamed stuck state `scope`). Also: running
  quoted escape-free code is the identity (L2.run.context).

  The headline theorems are `step-det`, `preservation`, `progress`,
  `safety` and `run-quote`."
  (:require [ansatz.core :as a]
            [klara.formal.core]
            [klara.formal.ws]))

;; ---------------------------------------------------------------------------
;; Relations and invariants

;; Step: the graph of `step`.
(a/inductive Step [] :in Prop :indices [c Config c2 Config]
  (mk [c Config] [c2 Config] [h (= (Option Config) (step c) (Option.some Config c2))] :where [c c2]))

(a/inductive WSW [] :in Prop :indices [w World]
  (empty :where [World.empty])
  (bind [id Nat] [v Tm] [rest World] [hv (WS 0 v)] [hr (WSW rest)] :where [(World.bind id v rest)]))

(a/inductive WSWs [] :in Prop :indices [ws Worlds]
  (none :where [Worlds.none])
  (more [w World] [rest Worlds] [hw (WSW w)] [hr (WSWs rest)] :where [(Worlds.more w rest)]))

(a/inductive WSC [] :in Prop :indices [c Config]
  (mk [w World] [ws Worlds] [n Nat] [t Tm] [hw (WSW w)] [hws (WSWs ws)] [ht (WS 0 t)]
      :where [(Config.mk w ws n t)]))

;; Outcome invariant: a step stays closed, an effect carries a closed argument
;; and a context closed but for its hole, and a stuck state is a named one.
(a/inductive OK [] :in Prop :indices [o Out]
  (val :where [Out.val])
  (next [n Nat] [e Tm] [he (WS 0 e)] :where [(Out.next n e)])
  (eff [op Nat] [v Tm] [k Tm] [hv (WS 0 v)] [hk (WS 1 k)] :where [(Out.eff op v k)])
  (stuck [s Stuck] [hs (Not (= Stuck s Stuck.scope))] :where [(Out.stuck s)])
  (chk [ns (List Nat)] [n Nat] [e Tm] [he (WS 0 e)] :where [(Out.chk ns n e)]))

;; ---------------------------------------------------------------------------
;; Determinism: Step is the graph of a function.

(a/theorem step-det [c :- Config, c1 :- Config, c2 :- Config, h1 :- (Step c c1), h2 :- (Step c c2)]
  (= c1 c2)
  (cases h1 :with [(mk x y ha) (cases h2 :with [(mk x2 y2 hb) (rw [ha] at hb) (cases hb) (rfl)])]))

;; ---------------------------------------------------------------------------
;; Lookup in closed worlds

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

(a/theorem worldAt-ws [ws :- Worlds, hws :- (WSWs ws)]
  (forall [i :- Nat] (forall [w :- World] (=> (= (Option World) (worldAt ws i) (Option.some World w)) (WSW w))))
  (induction hws)
  (all_goals (intro i) (intro wv) (intro h))
  (simp only [worldAt] at h) (cases h)
  (revert h) (cases i)
  (all_goals (simp only [worldAt]))
  (intro h2) (cases h2) (assumption)
  (intro h2) (exact (ih_hr _ wv h2)))

;; ---------------------------------------------------------------------------
;; The outcome invariant, piece by piece

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

(a/theorem stuck-ok [s :- Stuck, hs :- (Not (= Stuck s Stuck.scope))] (OK (Out.stuck s))
  (exact (OK.stuck s hs)))

(a/theorem stuck-notFn-ok [] (OK (Out.stuck Stuck.notFn)) (apply OK.stuck) (intro hh) (cases hh))
(a/theorem stuck-primType-ok [] (OK (Out.stuck Stuck.primType)) (apply OK.stuck) (intro hh) (cases hh))
(a/theorem stuck-overflow-ok [] (OK (Out.stuck Stuck.overflow)) (apply OK.stuck) (intro hh) (cases hh))
(a/theorem stuck-stage-ok [] (OK (Out.stuck Stuck.stage)) (apply OK.stuck) (intro hh) (cases hh))
(a/theorem stuck-extrusion-ok [] (OK (Out.stuck Stuck.extrusion)) (apply OK.stuck) (intro hh) (cases hh))
(a/theorem stuck-unbound-ok [id :- Nat] (OK (Out.stuck (Stuck.unbound id))) (apply OK.stuck) (intro hh) (cases hh))

(a/theorem betaLit-ok [n :- Nat, d :- Datum] (OK (betaLit n d))
  (cases d)
  (all_goals (simp only [betaLit]))
  (all_goals (try (apply stuck-notFn-ok)))
  (constructor) (constructor))

(a/theorem beta-ok [n :- Nat, f :- Tm, x :- Tm, hf :- (WS 0 f), hx :- (WS 0 x)]
  (OK (beta n f x))
  (cases hf)
  (all_goals (try (omega)))
  (all_goals (simp only [beta]))
  (all_goals (first (apply stuck-notFn-ok) (apply betaLit-ok) (constructor)))
  (all_goals (apply ws-subst))
  (all_goals (try (first (assumption) (omega))))
  (all_goals (apply ws-subst))
  (all_goals (try (first (assumption) (omega))))
  (all_goals (constructor))
  (all_goals (assumption)))

(a/theorem primResult-ok [n :- Nat, r :- PrimRes] (OK (primResult n r))
  (cases r)
  (all_goals (simp only [primResult]))
  (constructor) (constructor)
  (apply stuck-primType-ok)
  (apply stuck-overflow-ok))

(a/theorem primStep-ok [n :- Nat, op :- PrimOp, x :- Tm, y :- Tm]
  (OK (primStep n op x y))
  (cases x)
  (all_goals (try (simp only [primStep]) (apply stuck-primType-ok)))
  (cases y)
  (all_goals (try (simp only [primStep]) (apply stuck-primType-ok)))
  (simp only [primStep])
  (apply primResult-ok))

(a/theorem resolveResult-ok [n :- Nat, id :- Nat, r :- (Option Tm),
                             h :- (forall [v :- Tm] (=> (= (Option Tm) r (Option.some Tm v)) (WS 0 v)))]
  (OK (resolveResult n id r))
  (cases r)
  (all_goals (simp only [resolveResult]))
  (apply stuck-unbound-ok)
  (constructor) (apply h) (rfl))

(a/theorem pinValue-ok [n :- Nat, wi :- Nat, id :- Nat, r :- (Option Tm),
                         h :- (forall [v :- Tm] (=> (= (Option Tm) r (Option.some Tm v)) (WS 0 v)))]
  (OK (pinValue n wi id r))
  (cases r)
  (all_goals (simp only [pinValue]))
  (apply stuck-unbound-ok)
  (constructor) (apply ws-pinTm) (apply h) (rfl))

(a/theorem pinResult-ok [n :- Nat, wi :- Nat, id :- Nat, w :- (Option World),
                         h :- (forall [wv :- World] (=> (= (Option World) w (Option.some World wv)) (WSW wv)))]
  (OK (pinResult n wi id w))
  (cases w)
  (all_goals (simp only [pinResult]))
  (apply stuck-unbound-ok)
  (apply pinValue-ok) (apply lookup-ws) (apply h) (rfl))

(a/theorem handleEff-ok [n :- Nat, ops :- (List Nat), r :- Tm, o :- Tm, op :- Nat, v :- Tm, k :- Tm,
                         hr :- (WS 1 r), ho :- (WS 3 o), hv :- (WS 0 v), hk :- (WS 1 k)]
  (OK (handleEff n ops r o op v k))
  (have hr2 (WS 2 r)) (apply (ws-weaken 1 r hr)) (omega)
  (have ho4 (WS 4 o)) (apply (ws-weaken 3 o ho)) (omega)
  (have hh (WS 1 (Tm.handling ops k r o))) (constructor) (assumption) (assumption) (assumption)
  (have hl (WS 0 (Tm.lam (Tm.handling ops k r o)))) (constructor) (assumption)
  (have h2 (WS 2 (subst 0 (Tm.lam (Tm.handling ops k r o)) o))) (apply ws-subst) (assumption) (assumption) (omega)
  (have h1 (WS 1 (subst 0 v (subst 0 (Tm.lam (Tm.handling ops k r o)) o)))) (apply ws-subst) (assumption) (assumption) (omega)
  (simp only [handleEff])
  (split)
  (all_goals (constructor))
  (all_goals (try (assumption)))
  (apply ws-subst) (constructor) (assumption) (omega))

(a/theorem handlingOut-ok [n :- Nat, ops :- (List Nat), r :- Tm, o :- Tm, ob :- Out, b :- Tm,
                           hb :- (WS 0 b), hr :- (WS 1 r), ho :- (WS 3 o), hob :- (OK ob)]
  (OK (handlingOut n ops r o ob b))
  (cases hob)
  (all_goals (simp only [handlingOut]))
  (constructor) (apply ws-subst) (assumption) (assumption) (omega)
  (constructor) (constructor) (assumption) (assumption) (assumption)
  (apply handleEff-ok) (assumption) (assumption) (assumption) (assumption)
  (constructor) (assumption)
  (constructor) (constructor) (assumption) (assumption) (assumption))

(a/theorem ws-1-2 [t :- Tm, h :- (WS 1 t)] (WS 2 t)
  (apply (ws-weaken 1 t h)) (omega))

;; ---------------------------------------------------------------------------
;; Staging pieces

(a/theorem atZero-ok [l :- Nat, x :- Out, y :- Out, hx :- (OK x), hy :- (OK y)] (OK (atZero l x y))
  (cases l) (all_goals (simp only [atZero])) (all_goals (assumption)))

(a/theorem dropOut-ok [g :- Nat, k :- Nat, o :- Out, ho :- (OK o)] (OK (dropOut g k o))
  (cases ho) (all_goals (simp only [dropOut])) (all_goals (constructor)) (all_goals (assumption)))

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

(a/theorem openFix-ok [n :- Nat, fb :- Tm, hfb :- (WS 2 fb)] (OK (openFix n fb))
  (simp only [openFix]) (constructor) (constructor)
  (apply ws-subst) (constructor) (apply ws-subst) (constructor) (assumption) (omega) (omega))

(a/theorem openHandle-ok [n :- Nat, ops :- (List Nat), b :- Tm, r :- Tm, o :- Tm,
                          hb :- (WS 0 b), hr :- (WS 1 r), ho :- (WS 3 o)]
  (OK (openHandle n ops b r o))
  (simp only [openHandle]) (constructor) (constructor)
  (assumption)
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
  (cases heq (wsb 0 c))
  (all_goals (simp only [runCode, heq]))
  (apply stuck-extrusion-ok)
  (constructor) (exact (wsb-WS c 0 heq)))

(a/theorem runStep-ok [n :- Nat, u :- Tm] (OK (runStep n u))
  (cases u)
  (all_goals (simp only [runStep]))
  (all_goals (try (apply stuck-stage-ok)))
  (apply runCode-ok))

(a/theorem pick-ws [c :- Tm, u :- Tm, e :- Tm, hu :- (WS 0 u), he :- (WS 0 e)] (WS 0 (pick c u e))
  (simp only [pick]) (split) (all_goals (assumption)))

;; ---------------------------------------------------------------------------
;; One lemma per term constructor; the main induction only dispatches.

(a/theorem ev-lam-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, b :- Tm, hb :- (WS 1 b)]
  (OK (ev w ws n l (Tm.lam b)))
  (simp only [ev]) (apply atZero-ok) (constructor) (apply openLam-ok) (assumption))

(a/theorem ev-app-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, f :- Tm, x :- Tm, hf :- (WS 0 f), hx :- (WS 0 x),
                      of :- (OK (ev w ws n l f)), ox :- (OK (ev w ws n l x))]
  (OK (ev w ws n l (Tm.app f x)))
  (simp only [ev])
  (apply seq2-ok) (exact of) (exact ox)
  (apply atZero-ok) (apply beta-ok) (assumption) (assumption) (constructor)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-let-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, e :- Tm, b :- Tm, he :- (WS 0 e), hb :- (WS 1 b),
                      oe :- (OK (ev w ws n l e))]
  (OK (ev w ws n l (Tm.let_ e b)))
  (simp only [ev])
  (apply atZero-ok)
  (apply seq1-ok) (exact oe)
  (constructor) (apply ws-subst) (assumption) (assumption) (omega)
  (intro e2) (intro he2) (try (dsimp)) (constructor) (assumption) (assumption)
  (intro e2) (intro he2) (try (dsimp)) (constructor) (assumption) (apply ws-1-2) (assumption)
  (apply openLet-ok) (assumption) (assumption))

(a/theorem ev-if-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, c :- Tm, u :- Tm, e :- Tm,
                     hc :- (WS 0 c), hu :- (WS 0 u), he :- (WS 0 e),
                     oc :- (OK (ev w ws n l c)), ou :- (OK (ev w ws n l u)), oe :- (OK (ev w ws n l e))]
  (OK (ev w ws n l (Tm.if_ c u e)))
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

(a/theorem ev-letrec-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, fb :- Tm, b :- Tm, hfb :- (WS 2 fb), hb :- (WS 1 b)]
  (OK (ev w ws n l (Tm.letrec fb b)))
  (simp only [ev]) (apply atZero-ok)
  (constructor) (apply ws-subst) (constructor) (assumption) (assumption) (omega)
  (apply openLetrec-ok) (assumption) (assumption))

(a/theorem ev-fix-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, fb :- Tm, hfb :- (WS 2 fb)]
  (OK (ev w ws n l (Tm.fix fb)))
  (simp only [ev]) (apply atZero-ok) (constructor) (apply openFix-ok) (assumption))

(a/theorem ev-glob-ok [w :- World, hw :- (WSW w), ws :- Worlds, n :- Nat, l :- Nat, id :- Nat]
  (OK (ev w ws n l (Tm.glob id)))
  (simp only [ev]) (apply atZero-ok)
  (apply resolveResult-ok) (intro v0) (intro hl) (exact (lookup-ws w hw _ _ hl))
  (constructor))

(a/theorem ev-pin-ok [w :- World, ws :- Worlds, hws :- (WSWs ws), n :- Nat, l :- Nat, wi :- Nat, id :- Nat]
  (OK (ev w ws n l (Tm.pin wi id)))
  (simp only [ev]) (apply atZero-ok)
  (apply pinResult-ok) (intro wv) (intro hl) (exact (worldAt-ws ws hws _ _ hl))
  (constructor))

(a/theorem ev-prim-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, op :- PrimOp, x :- Tm, y :- Tm,
                       hx :- (WS 0 x), hy :- (WS 0 y),
                       ox :- (OK (ev w ws n l x)), oy :- (OK (ev w ws n l y))]
  (OK (ev w ws n l (Tm.prim op x y)))
  (simp only [ev])
  (apply seq2-ok) (exact ox) (exact oy)
  (apply atZero-ok) (apply primStep-ok) (constructor)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-perform-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, op :- Nat, x :- Tm, hx :- (WS 0 x),
                          ox :- (OK (ev w ws n l x))]
  (OK (ev w ws n l (Tm.perform op x)))
  (simp only [ev])
  (apply seq1-ok) (exact ox)
  (apply atZero-ok) (constructor) (assumption) (constructor) (omega) (constructor)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-handle-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, ops :- (List Nat), b :- Tm, r :- Tm, o :- Tm,
                         hb :- (WS 0 b), hr :- (WS 1 r), ho :- (WS 3 o)]
  (OK (ev w ws n l (Tm.handle ops b r o)))
  (simp only [ev]) (apply atZero-ok)
  (constructor) (constructor) (assumption) (assumption) (assumption)
  (apply openHandle-ok) (assumption) (assumption) (assumption))

(a/theorem ev-handling-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, ops :- (List Nat), b :- Tm, r :- Tm, o :- Tm,
                           hb :- (WS 0 b), hr :- (WS 1 r), ho :- (WS 3 o), ob :- (OK (ev w ws n l b))]
  (OK (ev w ws n l (Tm.handling ops b r o)))
  (simp only [ev]) (apply atZero-ok)
  (apply handlingOut-ok) (assumption) (assumption) (assumption) (exact ob)
  (apply stuck-stage-ok))

(a/theorem ev-code-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, u :- Tm, hu :- (WS 0 u),
                       ou :- (OK (ev w ws n (+ l 1) u))]
  (OK (ev w ws n l (Tm.code u)))
  (simp only [ev]) (apply frame-ok) (exact ou)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-esc-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, u :- Tm, hu :- (WS 0 u),
                      ou :- (OK (ev w ws n (- l 1) u))]
  (OK (ev w ws n l (Tm.esc u)))
  (simp only [ev]) (apply escOut-ok) (assumption) (exact ou))

(a/theorem ev-run-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, u :- Tm, hu :- (WS 0 u),
                      ou :- (OK (ev w ws n l u))]
  (OK (ev w ws n l (Tm.run_ u)))
  (simp only [ev]) (apply atZero-ok)
  (apply seq1-ok) (exact ou) (apply runStep-ok)
  (intro e) (intro he) (try (dsimp)) (constructor) (assumption)
  (intro e) (intro he) (try (dsimp)) (constructor) (assumption)
  (apply frame-ok) (exact ou)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-gvar-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, g :- Nat] (OK (ev w ws n l (Tm.gvar g)))
  (simp only [ev]) (apply atZero-ok) (constructor) (constructor) (constructor) (constructor))

(a/theorem ev-nlam-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, g :- Nat, b :- Tm, hb :- (WS 0 b),
                       ob :- (OK (ev w ws n l b))]
  (OK (ev w ws n l (Tm.nlam g b)))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply dropOut-ok) (apply frame-ok) (exact ob)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-nlet-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, g :- Nat, e :- Tm, b :- Tm,
                       he :- (WS 0 e), hb :- (WS 0 b), oe :- (OK (ev w ws n l e)), ob :- (OK (ev w ws n l b))]
  (OK (ev w ws n l (Tm.nlet g e b)))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply seq2-ok) (exact oe) (apply dropOut-ok) (exact ob) (constructor)
  (all_goals (intro e2) (intro he2) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-nletrec-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, g :- Nat, fb :- Tm, b :- Tm,
                          hfb :- (WS 0 fb), hb :- (WS 0 b), ofb :- (OK (ev w ws n l fb)), ob :- (OK (ev w ws n l b))]
  (OK (ev w ws n l (Tm.nletrec g fb b)))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply seq2-ok) (apply dropOut-ok) (exact ofb) (apply dropOut-ok) (exact ob) (constructor)
  (all_goals (intro e2) (intro he2) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

(a/theorem ev-nfix-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, g :- Nat, fb :- Tm, hfb :- (WS 0 fb),
                       ofb :- (OK (ev w ws n l fb))]
  (OK (ev w ws n l (Tm.nfix g fb)))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply dropOut-ok) (apply frame-ok) (exact ofb)
  (all_goals (intro e) (intro he) (try (dsimp)) (constructor) (assumption)))

(a/theorem ev-nhandle-ok [w :- World, ws :- Worlds, n :- Nat, l :- Nat, g :- Nat, ops :- (List Nat), b :- Tm, r :- Tm, o :- Tm,
                          hb :- (WS 0 b), hr :- (WS 0 r), ho :- (WS 0 o),
                          ob :- (OK (ev w ws n l b)), or :- (OK (ev w ws n l r)), oo :- (OK (ev w ws n l o))]
  (OK (ev w ws n l (Tm.nhandle g ops b r o)))
  (simp only [ev]) (apply atZero-ok) (apply stuck-stage-ok)
  (apply seq3-ok) (exact ob) (apply dropOut-ok) (exact or) (apply dropOut-ok) (exact oo) (constructor)
  (all_goals (intro e2) (intro he2) (try (dsimp)) (constructor))
  (all_goals (first (assumption) (and_then (apply ws-closed) (assumption)))))

;; The outcome of a closed term at any level, in closed worlds, satisfies the
;; invariant: every next and chk is closed, and no stuck state is `scope`.
;; This one induction carries both preservation and progress.
(a/theorem ev-ok [w :- World, hw :- (WSW w), ws :- Worlds, hws :- (WSWs ws), n :- Nat, t :- Tm]
  (forall [l :- Nat] (=> (WS 0 t) (OK (ev w ws n l t))))
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
  ;; letrec, fix
  (apply ev-letrec-ok) (assumption) (assumption)
  (apply ev-fix-ok) (assumption)
  ;; glob, pin
  (apply ev-glob-ok) (assumption)
  (apply ev-pin-ok) (assumption)
  ;; prim
  (apply ev-prim-ok) (assumption) (assumption) (apply ih_x) (assumption) (apply ih_y) (assumption)
  ;; perform
  (apply ev-perform-ok) (assumption) (apply ih_x) (assumption)
  ;; handle, handling
  (apply ev-handle-ok) (assumption) (assumption) (assumption)
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
  (apply ev-nfix-ok) (assumption) (apply ih_fb) (assumption)
  (apply ev-nhandle-ok) (assumption) (assumption) (assumption) (apply ih_b) (assumption) (apply ih_r) (assumption)
  (apply ih_o) (assumption))

(a/theorem run1-ok [w :- World, hw :- (WSW w), ws :- Worlds, hws :- (WSWs ws), n :- Nat, t :- Tm]
  (=> (WS 0 t) (OK (run1 w ws n t)))
  (intro ht) (simp only [run1]) (exact (ev-ok w hw ws hws n t 0 ht)))

(a/theorem stepOut-ok [w :- World, ws :- Worlds, o :- Out, w2 :- World, ws2 :- Worlds, n2 :- Nat, t2 :- Tm,
                       ho :- (OK o), hw :- (WSW w), hws :- (WSWs ws),
                       h :- (= (Option Config) (stepOut w ws o) (Option.some Config (Config.mk w2 ws2 n2 t2)))]
  (And (WSW w2) (And (WSWs ws2) (WS 0 t2)))
  (cases ho)
  (all_goals (simp only [stepOut] at h))
  (cases h)
  (cases h) (constructor) (assumption) (constructor) (assumption) (assumption)
  (cases h)
  (cases h)
  (revert h) (cases ns)
  (intro h) (simp only [chkStep] at h) (cases h) (constructor) (assumption) (constructor) (assumption) (assumption)
  (intro h) (simp only [chkStep] at h) (cases h))

;; ---------------------------------------------------------------------------
;; Preservation of well-scopedness.

(a/theorem preservation [w :- World, ws :- Worlds, n :- Nat, t :- Tm, w2 :- World, ws2 :- Worlds, n2 :- Nat, t2 :- Tm,
                         hs :- (Step (Config.mk w ws n t) (Config.mk w2 ws2 n2 t2)),
                         hw :- (WSW w), hws :- (WSWs ws), ht :- (WS 0 t)]
  (And (WSW w2) (And (WSWs ws2) (WS 0 t2)))
  (cases hs)
  (simp [step] at h)
  (exact (stepOut-ok w ws (run1 w ws n t) w2 ws2 n2 t2 (run1-ok w hw ws hws n t ht) hw hws h)))

;; ---------------------------------------------------------------------------
;; Progress modulo named stuck states.

(a/inductive Progress [] :in Prop :indices [c Config]
  (value [w World] [ws Worlds] [n Nat] [t Tm] [h (= Out (run1 w ws n t) Out.val)] :where [(Config.mk w ws n t)])
  (steps [c Config] [c2 Config] [h (Step c c2)] :where [c])
  (unhandled [w World] [ws Worlds] [n Nat] [t Tm] [op Nat] [v Tm] [k Tm]
             [h (= Out (run1 w ws n t) (Out.eff op v k))] :where [(Config.mk w ws n t)])
  (error [w World] [ws Worlds] [n Nat] [t Tm] [s Stuck] [h (= Out (run1 w ws n t) (Out.stuck s))]
         [hs (Not (= Stuck s Stuck.scope))] :where [(Config.mk w ws n t)])
  (extrusion [w World] [ws Worlds] [n Nat] [t Tm] [g Nat] [gs (List Nat)] [n2 Nat] [e Tm]
             [h (= Out (run1 w ws n t) (Out.chk (List.cons Nat g gs) n2 e))] :where [(Config.mk w ws n t)]))

(a/theorem progress-next [w :- World, ws :- Worlds, n :- Nat, t :- Tm, n2 :- Nat, e2 :- Tm]
  (=> (= Out (run1 w ws n t) (Out.next n2 e2)) (Progress (Config.mk w ws n t)))
  (intro hq)
  (have hs (= (Option Config) (step (Config.mk w ws n t)) (Option.some Config (Config.mk w ws n2 e2))))
  (simp [step, hq, stepOut])
  (exact (Progress.steps (Config.mk w ws n t) (Config.mk w ws n2 e2)
           (Step.mk (Config.mk w ws n t) (Config.mk w ws n2 e2) hs))))

(a/theorem progress-eff [w :- World, ws :- Worlds, n :- Nat, t :- Tm, op :- Nat, v :- Tm, k :- Tm]
  (=> (= Out (run1 w ws n t) (Out.eff op v k)) (Progress (Config.mk w ws n t)))
  (intro hq) (exact (Progress.unhandled w ws n t op v k hq)))

(a/theorem progress-stuck [w :- World, ws :- Worlds, n :- Nat, t :- Tm, s :- Stuck, hs :- (Not (= Stuck s Stuck.scope))]
  (=> (= Out (run1 w ws n t) (Out.stuck s)) (Progress (Config.mk w ws n t)))
  (intro hq) (exact (Progress.error w ws n t s hq hs)))

(a/theorem progress-val [w :- World, ws :- Worlds, n :- Nat, t :- Tm]
  (=> (= Out (run1 w ws n t) Out.val) (Progress (Config.mk w ws n t)))
  (intro hq) (exact (Progress.value w ws n t hq)))

(a/theorem progress-chk [w :- World, ws :- Worlds, n :- Nat, t :- Tm, ns :- (List Nat), n2 :- Nat, e2 :- Tm]
  (=> (= Out (run1 w ws n t) (Out.chk ns n2 e2)) (Progress (Config.mk w ws n t)))
  (intro hq)
  (cases ns)
  (have hs (= (Option Config) (step (Config.mk w ws n t)) (Option.some Config (Config.mk w ws n2 e2))))
  (simp [step, hq, stepOut, chkStep])
  (exact (Progress.steps (Config.mk w ws n t) (Config.mk w ws n2 e2)
           (Step.mk (Config.mk w ws n t) (Config.mk w ws n2 e2) hs)))
  (exact (Progress.extrusion w ws n t head tail n2 e2 hq)))

(a/theorem progress [w :- World, ws :- Worlds, n :- Nat, t :- Tm, hw :- (WSW w), hws :- (WSWs ws), ht :- (WS 0 t)]
  (Progress (Config.mk w ws n t))
  (have hok (OK (run1 w ws n t))) (exact (run1-ok w hw ws hws n t ht))
  (cases heq (run1 w ws n t))
  (revert heq) (apply progress-val)
  (revert heq) (apply progress-next)
  (revert heq) (apply progress-eff)
  (have hs (Not (= Stuck s Stuck.scope))) (rw [heq] at hok) (cases hok) (assumption)
  (revert heq) (apply progress-stuck) (assumption)
  (revert heq) (apply progress-chk))

;; ---------------------------------------------------------------------------
;; Safety on configurations.

(a/inductive Star [] :in Prop :indices [c Config c2 Config]
  (refl [c Config] :where [c c])
  (step [c Config] [c2 Config] [c3 Config] [h (Step c c2)] [hs (Star c2 c3)] :where [c c3]))

(a/theorem preservation-config [c :- Config, c2 :- Config, hs :- (Step c c2), hc :- (WSC c)]
  (WSC c2)
  (cases hc :with
    [(mk w ws n t hw hws ht)
     (cases c2 :with
       [(mk w2 ws2 n2 t2)
        (have hp (And (WSW w2) (And (WSWs ws2) (WS 0 t2)))) (exact (preservation w ws n t w2 ws2 n2 t2 hs hw hws ht))
        (exact (WSC.mk w2 ws2 n2 t2 (And.left hp) (And.left (And.right hp)) (And.right (And.right hp))))])]))

(a/theorem progress-config [c :- Config, hc :- (WSC c)]
  (Progress c)
  (cases hc :with [(mk w ws n t hw hws ht) (exact (progress w ws n t hw hws ht))]))

;; Safety: a closed configuration never reaches the unnamed stuck state.
(a/theorem safety [c :- Config, c2 :- Config, hc :- (WSC c), hs :- (Star c c2)]
  (Progress c2)
  (induction hs)
  (all_goals (try (exact (progress-config _ hc))))
  (exact (ih_hs (preservation-config _ _ h hc))))

;; ---------------------------------------------------------------------------
;; Running quoted code (L2.run.context): for a term without binders or escapes,
;; (run (code t)) steps to t in one step. Building it creates no names, so the
;; code value is t itself, and run's closedness check passes.

(a/inductive Quotable [] :in Prop :indices [t Tm]
  (lit [d Datum] :where [(Tm.lit d)])
  (glob [id Nat] :where [(Tm.glob id)])
  (app [f Tm] [x Tm] [hf (Quotable f)] [hx (Quotable x)] :where [(Tm.app f x)])
  (if_ [c Tm] [u Tm] [e Tm] [hc (Quotable c)] [hu (Quotable u)] [he (Quotable e)] :where [(Tm.if_ c u e)])
  (prim [op PrimOp] [x Tm] [y Tm] [hx (Quotable x)] [hy (Quotable y)] :where [(Tm.prim op x y)])
  (perform [op Nat] [x Tm] [hx (Quotable x)] :where [(Tm.perform op x)]))

(a/theorem quotable-built [w :- World, ws :- Worlds, n :- Nat, t :- Tm, l :- Nat, h :- (Quotable t)]
  (= Out (ev w ws n (+ l 1) t) Out.val)
  (induction h)
  (all_goals (simp only [ev]))
  (all_goals (try (simp only [atZero])))
  (all_goals (try (rw [ih_hf, ih_hx])))
  (all_goals (try (rw [ih_hc, ih_hu, ih_he])))
  (all_goals (try (rw [ih_hx, ih_hy])))
  (all_goals (try (rw [ih_hx])))
  (all_goals (try (rfl))))

(a/theorem quotable-toDB [t :- Tm, h :- (Quotable t)] (= Tm (toDB t) t)
  (induction h)
  (all_goals (simp [toDB]))
  (all_goals (try (simp_all))))

(a/theorem quotable-wsb [t :- Tm, h :- (Quotable t)] (forall [m :- Nat] (= Bool (wsb m t) true))
  (induction h)
  (all_goals (intro m))
  (all_goals (simp [wsb]))
  (all_goals (try (simp_all))))

(a/theorem run-quote [w :- World, ws :- Worlds, n :- Nat, t :- Tm, h :- (Quotable t)]
  (Step (Config.mk w ws n (Tm.run_ (Tm.code t))) (Config.mk w ws n t))
  (have hb (= Out (ev w ws n 1 t) Out.val)) (exact (quotable-built w ws n t 0 h))
  (have hd (= Tm (toDB t) t)) (exact (quotable-toDB t h))
  (have hw (= Bool (wsb 0 t) true)) (exact (quotable-wsb t h 0))
  (have r (= (Option Config) (step (Config.mk w ws n (Tm.run_ (Tm.code t))))
             (Option.some Config (Config.mk w ws n t))))
  (simp only [step run1 ev atZero frame seq1 runStep runCode]) (try (simp only [ev])) (rw [hb]) (simp only [frame seq1 runStep runCode hd hw]) (try (rw [hd])) (try (rw [hw])) (try (rfl))
  (exact (Step.mk _ _ r)))
