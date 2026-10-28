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
