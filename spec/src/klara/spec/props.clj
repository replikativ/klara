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

;; Well-scoped worlds. (A well-scoped configuration is stated directly as
;; WSW w /\ WS 0 t: an indexed `WSC (Config.mk w n t)` hits an ansatz recursor
;; generation error, see README.)
(a/inductive WSW [] :in Prop :indices [w World]
  (empty :where [World.empty])
  (bind [id Nat] [v Tm] [rest World] [hv (WS 0 v)] [hr (WSW rest)] :where [(World.bind id v rest)]))

;; Outcome invariant: a step stays closed, an effect carries a closed argument
;; and a context closed but for its hole, and a stuck state is a named one.
(a/inductive OK [] :in Prop :indices [o Out]
  (val :where [Out.val])
  (next [n Nat] [e Tm] [he (WS 0 e)] :where [(Out.next n e)])
  (eff [tg (Option Nat)] [op Nat] [v Tm] [k Tm] [hv (WS 0 v)] [hk (WS 1 k)] :where [(Out.eff tg op v k)])
  (stuck [s Stuck] [hs (Not (= Stuck s Stuck.scope))] :where [(Out.stuck s)]))

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
  (all_goals (intro id) (intro v) (intro h))
  (try (simp only [lookup] at h))
  (cases h)
  (revert h)
  (simp only [lookup])
  (split)
  (all_goals (dsimp) (intro h2))
  (exact (ih_hr _ _ h2))
  (cases h2) (assumption))

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
  (constructor) (assumption))

(a/theorem ws-1-2 [t :- Tm, h :- (WS 1 t)] (WS 2 t)
  (apply (ws-weaken 1 t h)) (omega))

;; The outcome of a closed term in a closed world satisfies the invariant.
;; This one induction carries both preservation and progress: every `next`
;; is closed, and no stuck state is the unnamed `scope`.
(a/theorem run1-ok [w :- World, hw :- (WSW w), n :- Nat, t :- Tm]
  (=> (WS 0 t) (OK (run1 w n t)))
  (induction t)
  (all_goals (intro ht))
  (all_goals (cases ht))
  (all_goals (try (omega)))
  (all_goals (simp [run1]))
  (all_goals (try (constructor)))
  (all_goals (try (first (apply seq2-ok) (apply seq1-ok) (apply handlingOut-ok) (apply resolveResult-ok))))
  (all_goals (try (first (apply ih_f) (apply ih_x) (apply ih_e) (apply ih_c) (apply ih_y) (apply ih_h)
                         (apply ih_p) (apply ih_m) (apply ih_b))))
  (all_goals (try (assumption)))
  (all_goals (try (first (apply beta-ok) (apply primStep-ok) (apply performStep-ok))))
  (all_goals (try (assumption)))
  ;; the resolve case
  (all_goals (try (intro v0) (intro hl) (exact (lookup-ws w hw _ _ hl))))
  ;; frames
  (all_goals (try (intro e2) (intro he2)))
  (all_goals (try (dsimp)))
  (all_goals (try (split)))
  (all_goals (try (constructor)))
  (all_goals (try (first (assumption) (and_then (apply ws-1-2) (assumption))
                         (and_then (apply ws-closed) (assumption)) (apply ws-substF') (constructor))))
  (all_goals (try (first (assumption) (omega) (and_then (apply ws-closed) (assumption)) (constructor))))
  (all_goals (try (first (assumption) (omega) (and_then (apply ws-closed) (assumption)) (constructor))))
  (all_goals (try (first (assumption) (omega) (and_then (apply ws-closed) (assumption)) (constructor))))
  (all_goals (try (first (assumption) (omega)))))

;; ---------------------------------------------------------------------------
;; Only values have outcome `val`.

(a/theorem seq2-ne [o1 :- Out, o2 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), done :- Out,
                    hd :- (Not (= Out done Out.val))]
  (Not (= Out (seq2 o1 o2 fr1 fr2 done) Out.val))
  (intro h)
  (cases o1)
  (all_goals (try (simp [seq2, frame] at h)))
  (cases o2)
  (all_goals (try (simp [frame] at h)))
  (apply hd) (exact h))

(a/theorem seq1-ne [o :- Out, fr :- (=> Tm Tm), done :- Out, hd :- (Not (= Out done Out.val))]
  (Not (= Out (seq1 o fr done) Out.val))
  (intro h)
  (cases o)
  (all_goals (try (simp [seq1, frame] at h)))
  (apply hd) (exact h))

(a/theorem beta-ne [n :- Nat, f :- Tm, x :- Tm] (Not (= Out (beta n f x) Out.val))
  (intro h) (cases f) (all_goals (simp [beta] at h)) (all_goals (cases h)))

(a/theorem primResult-ne [n :- Nat, r :- (Option Datum)] (Not (= Out (primResult n r) Out.val))
  (intro h) (cases r) (all_goals (simp [primResult] at h)) (all_goals (cases h)))

(a/theorem primStep-ne [n :- Nat, op :- PrimOp, x :- Tm, y :- Tm] (Not (= Out (primStep n op x y) Out.val))
  (intro h)
  (cases x) (all_goals (try (simp [primStep] at h)))
  (cases y) (all_goals (try (simp [primStep] at h)))
  (revert h) (apply primResult-ne))

(a/theorem performStep-ne [op :- Nat, hh :- Tm, x :- Tm] (Not (= Out (performStep op hh x) Out.val))
  (intro h)
  (cases hh) (all_goals (try (simp [performStep] at h)))
  (cases d) (all_goals (try (simp [performStep] at h))))

(a/theorem handleEff-ne [n :- Nat, l :- Nat, r :- Tm, o :- Tm, tg :- (Option Nat), op :- Nat, v :- Tm, k :- Tm]
  (Not (= Out (handleEff n l r o tg op v k) Out.val))
  (intro h)
  (cases tg) (all_goals (try (simp [handleEff] at h)))
  (revert h) (split) (all_goals (dsimp)) (all_goals (intro h)) (all_goals (cases h)))

(a/theorem handlingOut-ne [n :- Nat, l :- Nat, b :- Tm, r :- Tm, o :- Tm, ob :- Out]
  (Not (= Out (handlingOut n l b r o ob) Out.val))
  (intro h)
  (cases ob) (all_goals (try (simp [handlingOut] at h)))
  (revert h) (apply handleEff-ne))

(a/theorem stepOut-ok [w :- World, o :- Out, w2 :- World, n2 :- Nat, t2 :- Tm,
                       ho :- (OK o), hw :- (WSW w),
                       h :- (= (Option Config) (stepOut w o) (Option.some Config (Config.mk w2 n2 t2)))]
  (And (WSW w2) (WS 0 t2))
  (cases ho)
  (all_goals (simp [stepOut] at h))
  (all_goals (cases h))
  (constructor) (assumption) (assumption))

;; ---------------------------------------------------------------------------
;; (c) Preservation of well-scopedness.

(a/theorem preservation [w :- World, n :- Nat, t :- Tm, w2 :- World, n2 :- Nat, t2 :- Tm,
                         hs :- (Step (Config.mk w n t) (Config.mk w2 n2 t2)),
                         hw :- (WSW w), ht :- (WS 0 t)]
  (And (WSW w2) (WS 0 t2))
  (cases hs)
  (simp [step] at h)
  (exact (stepOut-ok w (run1 w n t) w2 n2 t2 (run1-ok w hw n t ht) hw h)))

(a/theorem resolveResult-ne [n :- Nat, id :- Nat, r :- (Option Tm)] (Not (= Out (resolveResult n id r) Out.val))
  (intro h) (cases r) (all_goals (simp [resolveResult] at h)) (all_goals (cases h)))

(a/theorem run1-val [w :- World, n :- Nat, t :- Tm, hq :- (= Out (run1 w n t) Out.val)]
  (= Bool (isVal t) true)
  (cases t)
  (all_goals (try (rfl)))
  (all_goals (try (simp [run1] at hq)))
  (all_goals (exfalso) (revert hq))
  (all_goals (first (apply seq2-ne) (apply seq1-ne) (apply handlingOut-ne) (apply resolveResult-ne)))
  (all_goals (try (first (apply beta-ne) (apply primStep-ne) (apply performStep-ne))))
  (all_goals (intro hh) (cases hh)))

(a/theorem isVal-run1 [w :- World, n :- Nat, t :- Tm, h :- (= Bool (isVal t) Bool.true)]
  (= Out (run1 w n t) Out.val)
  (cases t)
  (all_goals (try (simp [isVal] at h)))
  (all_goals (simp [run1])))

;; ---------------------------------------------------------------------------
;; (b) Progress modulo named stuck states.
;;
;; A closed configuration is a value, steps, is an effect no handler instance
;; in its context catches (an ambient op at top level, or a capability that
;; escaped its instance), or is a named error. The unnamed failure `scope`
;; is excluded.

(a/inductive Progress [] :in Prop :indices [c Config]
  (value [w World] [n Nat] [t Tm] [h (= Bool (isVal t) Bool.true)] :where [(Config.mk w n t)])
  (steps [c Config] [c2 Config] [h (Step c c2)] :where [c])
  (unhandled [w World] [n Nat] [t Tm] [tg (Option Nat)] [op Nat] [v Tm] [k Tm]
             [h (= Out (run1 w n t) (Out.eff tg op v k))] :where [(Config.mk w n t)])
  (error [w World] [n Nat] [t Tm] [s Stuck] [h (= Out (run1 w n t) (Out.stuck s))]
         [hs (Not (= Stuck s Stuck.scope))] :where [(Config.mk w n t)]))

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
  (intro hq) (exact (Progress.value w n t (run1-val w n t hq))))

(a/theorem progress [w :- World, n :- Nat, t :- Tm, hw :- (WSW w), ht :- (WS 0 t)]
  (Progress (Config.mk w n t))
  (have hok (OK (run1 w n t))) (exact (run1-ok w hw n t ht))
  (cases heq (run1 w n t))
  (revert heq) (apply progress-val)
  (revert heq) (apply progress-next)
  (revert heq) (apply progress-eff)
  (have hs (Not (= Stuck s Stuck.scope))) (rw [heq] at hok) (cases hok) (assumption)
  (revert heq) (apply progress-stuck) (assumption))

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
  (have rp (= Out (run1 w n p) Out.val)) (exact (isVal-run1 w n p vp))
  (have rm (= Out (run1 w n m) Out.val)) (exact (isVal-run1 w n m vm))
  (have rx (= Out (run1 w n x) Out.val)) (exact (isVal-run1 w n x vx))
  (have r1 (= (Option Config) (step (Config.mk w n (Tm.app (Tm.specialize p m) x)))
              (Option.some Config (Config.mk w n (Tm.app (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0))) x)))))
  (simp [step, stepOut, run1, seq2, frame, rp, rm, rx])
  (exact (Step.mk _ _ r1)))

;; ... which, applied to a value, beta-reduces to (p m x): p and m are closed.
(a/theorem smn-step2 [w :- World, n :- Nat, p :- Tm, m :- Tm, x :- Tm,
                      hp :- (WS 0 p), hm :- (WS 0 m), vx :- (= Bool (isVal x) Bool.true)]
  (Step (Config.mk w n (Tm.app (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0))) x))
        (Config.mk w n (Tm.app (Tm.app p m) x)))
  (have rx (= Out (run1 w n x) Out.val)) (exact (isVal-run1 w n x vx))
  (have cp (= Tm (substF x p 0) p)) (exact (substF-closed x p 0 hp))
  (have cm (= Tm (substF x m 0) m)) (exact (substF-closed x m 0 hm))
  (have r2 (= (Option Config) (step (Config.mk w n (Tm.app (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0))) x)))
              (Option.some Config (Config.mk w n (Tm.app (Tm.app p m) x)))))
  (simp [step, stepOut, run1, seq2, frame, rx, beta, subst, substF, substVar, cp, cm])
  (rw [cp, cm])
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
