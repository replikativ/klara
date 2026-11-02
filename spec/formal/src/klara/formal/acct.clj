(ns klara.formal.acct
  "λ-acct: the accounting calculus (design/11-profiles.md, spec/formal/README.md).
  A small calculus of its own, separate from the core model (core.clj), so
  that tokens, exceptions and the affine judgment do not touch the core
  metatheory: functions, let, if, account tokens over one resource, deep
  multi-shot handlers by operation name (as in core) and exceptions.

  A configuration is a store and a term. The store is the wallet (what the
  context may still grant), what was spent, the next token id and the live
  tokens (id and amount). A token in a term is a reference `tok i` to a live
  entry, so copying a term (a continuation resumed twice, a value used twice)
  copies references, never authority. The token operations are the only
  steps that change the store, each a balanced transfer; a raise drops its
  context and leaves the store alone, so a token the raise skipped stays
  live (leaked until its job settles, design/10-accounting.md).

  `ev` takes a flag: checked (true) is Klara's semantics, where using a token
  that is not live is the stuck state `reuse` (L3.affine.reuse); unchecked
  (false) is what code compiled with the check erased does (it proceeds with
  amount 0). acct_typing.clj proves that on configurations reached by typed
  programs the two agree (check erasure).

  Representation: de Bruijn indices; substitution of closed values, as in
  core."
  (:require [ansatz.core :as a]))

;; Load Lean's Init once: another model may already have loaded it, and
;; loading replaces the environment with everything declared in it.
(when-not (some-> (try (a/env) (catch Exception _ nil)) (.lookup (ansatz.kernel.name/from-string "Nat.add")))
  (a/load-init!))

;; ---------------------------------------------------------------------------
;; Syntax

(a/inductive Acct.Datum []
  (nil)
  (bool [b Bool])
  (num [n Nat]))

;; Binding structure (de Bruijn variables each sub-term binds):
;;   lam b               b: 1
;;   let_ e b            b: 1
;;   try_ b h            h: 1 (the raised value)
;;   handle ops b r o    r: 1 (the value), o: 3 (2 = op, 1 = argument, 0 = k)
;;   handling ops b r o  as handle (runtime: an installed handler frame)
(a/inductive Acct.Tm []
  (var [i Nat])
  (lit [d Acct.Datum])
  (lam [b Acct.Tm])
  (app [f Acct.Tm] [x Acct.Tm])
  (let_ [e Acct.Tm] [b Acct.Tm])
  (if_ [c Acct.Tm] [u Acct.Tm] [e Acct.Tm])
  (tok [i Nat])                                            ; runtime: a token reference
  (take [x Acct.Tm])                                       ; (account/take n)
  (spend [u Acct.Tm] [x Acct.Tm])                          ; (account/spend t n)
  (join [u Acct.Tm] [v Acct.Tm])                           ; (account/join t1 t2)
  (put [u Acct.Tm])                                        ; (account/put t)
  (raise [x Acct.Tm])                                      ; (throw x)
  (try_ [b Acct.Tm] [h Acct.Tm])                           ; (try b (catch _ e h))
  (perform [op Nat] [x Acct.Tm])
  (handle [ops (List Nat)] [b Acct.Tm] [r Acct.Tm] [o Acct.Tm])
  (handling [ops (List Nat)] [b Acct.Tm] [r Acct.Tm] [o Acct.Tm]))

;; ---------------------------------------------------------------------------
;; The store

(a/inductive Acct.Live []
  (nil)
  (cons [id Nat] [amt Nat] [rest Acct.Live]))

(a/inductive Acct.Store []
  (mk [wallet Nat] [spent Nat] [next Nat] [live Acct.Live]))

(a/defn Acct.find [l :- Acct.Live, i :- Nat] (Option Nat)
  (match l
    [nil (Option.none Nat)]
    [(cons k m rest) (match (Nat.beq k i) [true (Option.some Nat m)] [false (Acct.find rest i)])]))

(a/defn Acct.remove [l :- Acct.Live, i :- Nat] Acct.Live
  (match l
    [nil Acct.Live.nil]
    [(cons k m rest) (match (Nat.beq k i) [true rest] [false (Acct.Live.cons k m (Acct.remove rest i))])]))

(a/defn Acct.total [l :- Acct.Live] Nat
  (match l
    [nil 0]
    [(cons k m rest) (+ m (Acct.total rest))]))

;; minted = wallet + spent + held in live tokens (L3.account.conservation)
(a/defn Acct.minted [s :- Acct.Store] Nat
  (match s [(mk w sp nx l) (+ w (+ sp (Acct.total l)))]))

;; ---------------------------------------------------------------------------
;; Substitution of a closed value

(a/defn Acct.substVar [v :- Acct.Tm, i :- Nat, j :- Nat] Acct.Tm
  (match (Nat.beq i j)
    [true v]
    [false (match (Nat.blt j i) [true (Acct.Tm.var (- i 1))] [false (Acct.Tm.var i)])]))

(a/defn Acct.subst [j :- Nat, v :- Acct.Tm, t :- Acct.Tm] Acct.Tm
  (match t
    [(var i) (Acct.substVar v i j)]
    [(lit d) (Acct.Tm.lit d)]
    [(lam b) (Acct.Tm.lam (Acct.subst (+ j 1) v b))]
    [(app f x) (Acct.Tm.app (Acct.subst j v f) (Acct.subst j v x))]
    [(let_ e b) (Acct.Tm.let_ (Acct.subst j v e) (Acct.subst (+ j 1) v b))]
    [(if_ c u e) (Acct.Tm.if_ (Acct.subst j v c) (Acct.subst j v u) (Acct.subst j v e))]
    [(tok i) (Acct.Tm.tok i)]
    [(take x) (Acct.Tm.take (Acct.subst j v x))]
    [(spend u x) (Acct.Tm.spend (Acct.subst j v u) (Acct.subst j v x))]
    [(join u w) (Acct.Tm.join (Acct.subst j v u) (Acct.subst j v w))]
    [(put u) (Acct.Tm.put (Acct.subst j v u))]
    [(raise x) (Acct.Tm.raise (Acct.subst j v x))]
    [(try_ b h) (Acct.Tm.try_ (Acct.subst j v b) (Acct.subst (+ j 1) v h))]
    [(perform op x) (Acct.Tm.perform op (Acct.subst j v x))]
    [(handle ops b r o) (Acct.Tm.handle ops (Acct.subst j v b) (Acct.subst (+ j 1) v r) (Acct.subst (+ j 3) v o))]
    [(handling ops b r o) (Acct.Tm.handling ops (Acct.subst j v b) (Acct.subst (+ j 1) v r) (Acct.subst (+ j 3) v o))]))

;; Clojure truthiness (L0.eval.truth).
(a/defn Acct.truthy [t :- Acct.Tm] Bool
  (match t
    [(lit d) (match d [nil false] [(bool b) b] [_ true])]
    [_ true]))

(a/defn Acct.pick [c :- Acct.Tm, u :- Acct.Tm, e :- Acct.Tm] Acct.Tm
  (match (Acct.truthy c) [true u] [false e]))

(a/defn Acct.member [x :- Nat, l :- (List Nat)] Bool
  (match l
    [nil false]
    [(cons y r) (match (Nat.beq x y) [true true] [false (Acct.member x r)])]))

;; ---------------------------------------------------------------------------
;; One step

(a/inductive Acct.Stuck []
  (scope)          ; a free variable: excluded by typing
  (notFn)          ; L0.eval.not-fn
  (primType)       ; an operation given the wrong kind of value
  (insufficient)   ; L3.account.insufficient: more than the wallet or the token holds
  (reuse))         ; L3.affine.reuse: a token that is not live

;;   val          the term is a value
;;   next s e     steps to e with store s
;;   eff op v k   the term is E[perform op v], E does not handle op, k = E[var 0]
;;   exn v        the term is E[raise v], E does not catch it
;;   stuck s      a named stuck state
(a/inductive Acct.Out []
  (val)
  (next [s Acct.Store] [e Acct.Tm])
  (eff [op Nat] [v Acct.Tm] [k Acct.Tm])
  (exn [v Acct.Tm])
  (stuck [s Acct.Stuck]))

(a/defn Acct.frame [o :- Acct.Out, fr :- (=> Acct.Tm Acct.Tm)] Acct.Out
  (match o
    [val Acct.Out.val]
    [(next s e) (Acct.Out.next s (fr e))]
    [(eff op v k) (Acct.Out.eff op v (fr k))]
    [(exn v) (Acct.Out.exn v)]
    [(stuck s) (Acct.Out.stuck s)]))

(a/defn Acct.seq1 [o :- Acct.Out, fr :- (=> Acct.Tm Acct.Tm), done :- Acct.Out] Acct.Out
  (match o [val done] [_ (Acct.frame o fr)]))

(a/defn Acct.seq2 [o1 :- Acct.Out, o2 :- Acct.Out, fr1 :- (=> Acct.Tm Acct.Tm), fr2 :- (=> Acct.Tm Acct.Tm),
                   done :- Acct.Out] Acct.Out
  (match o1
    [val (match o2 [val done] [_ (Acct.frame o2 fr2)])]
    [_ (Acct.frame o1 fr1)]))

(a/defn Acct.beta [s :- Acct.Store, f :- Acct.Tm, x :- Acct.Tm] Acct.Out
  (match f
    [(lam b) (Acct.Out.next s (Acct.subst 0 x b))]
    [_ (Acct.Out.stuck Acct.Stuck.notFn)]))

;; The amount a token holds: checked, a token that is not live is none;
;; unchecked (the check erased), it is taken to hold 0.
(a/defn Acct.held [c :- Bool, l :- Acct.Live, i :- Nat] (Option Nat)
  (match c
    [true (Acct.find l i)]
    [false (match (Acct.find l i) [none (Option.some Nat 0)] [(some m) (Option.some Nat m)])]))

(a/defn Acct.amount [x :- Acct.Tm] (Option Nat)
  (match x
    [(lit d) (match d [(num n) (Option.some Nat n)] [_ (Option.none Nat)])]
    [_ (Option.none Nat)]))

;; take n: from the wallet into a new token (L3.account.token)
(a/defn Acct.takeN [s :- Acct.Store, n :- Nat] Acct.Out
  (match s
    [(mk w sp nx l)
     (match (Nat.ble n w)
       [true (Acct.Out.next (Acct.Store.mk (- w n) sp (+ nx 1) (Acct.Live.cons nx n l)) (Acct.Tm.tok nx))]
       [false (Acct.Out.stuck Acct.Stuck.insufficient)])]))

(a/defn Acct.takeStep [s :- Acct.Store, x :- Acct.Tm] Acct.Out
  (match (Acct.amount x)
    [none (Acct.Out.stuck Acct.Stuck.primType)]
    [(some n) (Acct.takeN s n)]))

;; spend t n: n goes to the sink, the rest into a new token
(a/defn Acct.spendH [s :- Acct.Store, i :- Nat, n :- Nat, h :- (Option Nat)] Acct.Out
  (match h
    [none (Acct.Out.stuck Acct.Stuck.reuse)]
    [(some m)
     (match s
       [(mk w sp nx l)
        (match (Nat.ble n m)
          [true (Acct.Out.next (Acct.Store.mk w (+ sp n) (+ nx 1) (Acct.Live.cons nx (- m n) (Acct.remove l i)))
                               (Acct.Tm.tok nx))]
          [false (Acct.Out.stuck Acct.Stuck.insufficient)])])]))

(a/defn Acct.spendN [c :- Bool, s :- Acct.Store, i :- Nat, x :- Acct.Tm] Acct.Out
  (match (Acct.amount x)
    [none (Acct.Out.stuck Acct.Stuck.primType)]
    [(some n) (match s [(mk w sp nx l) (Acct.spendH s i n (Acct.held c l i))])]))

(a/defn Acct.spendStep [c :- Bool, s :- Acct.Store, u :- Acct.Tm, x :- Acct.Tm] Acct.Out
  (match u
    [(tok i) (Acct.spendN c s i x)]
    [_ (Acct.Out.stuck Acct.Stuck.primType)]))

;; join t1 t2: one token holding both (refusing the same token twice)
(a/defn Acct.joinH [s :- Acct.Store, i :- Nat, j :- Nat, h1 :- (Option Nat), h2 :- (Option Nat)] Acct.Out
  (match h1
    [none (Acct.Out.stuck Acct.Stuck.reuse)]
    [(some m1)
     (match h2
       [none (Acct.Out.stuck Acct.Stuck.reuse)]
       [(some m2)
        (match s
          [(mk w sp nx l)
           (Acct.Out.next (Acct.Store.mk w sp (+ nx 1) (Acct.Live.cons nx (+ m1 m2) (Acct.remove (Acct.remove l i) j)))
                          (Acct.Tm.tok nx))])])]))

(a/defn Acct.joinN [c :- Bool, s :- Acct.Store, i :- Nat, j :- Nat] Acct.Out
  (match (Bool.and c (Nat.beq i j))
    [true (Acct.Out.stuck Acct.Stuck.reuse)]
    [false (match s [(mk w sp nx l) (Acct.joinH s i j (Acct.held c l i) (Acct.held c l j))])]))

(a/defn Acct.joinStep [c :- Bool, s :- Acct.Store, u :- Acct.Tm, v :- Acct.Tm] Acct.Out
  (match u
    [(tok i) (match v [(tok j) (Acct.joinN c s i j)] [_ (Acct.Out.stuck Acct.Stuck.primType)])]
    [_ (Acct.Out.stuck Acct.Stuck.primType)]))

;; put t: back into the wallet
(a/defn Acct.putH [s :- Acct.Store, i :- Nat, h :- (Option Nat)] Acct.Out
  (match h
    [none (Acct.Out.stuck Acct.Stuck.reuse)]
    [(some m)
     (match s
       [(mk w sp nx l) (Acct.Out.next (Acct.Store.mk (+ w m) sp nx (Acct.remove l i)) (Acct.Tm.lit Acct.Datum.nil))])]))

(a/defn Acct.putStep [c :- Bool, s :- Acct.Store, u :- Acct.Tm] Acct.Out
  (match u
    [(tok i) (match s [(mk w sp nx l) (Acct.putH s i (Acct.held c l i))])]
    [_ (Acct.Out.stuck Acct.Stuck.primType)]))

;; try: a raised value runs the handler; everything else passes through.
(a/defn Acct.tryOut [s :- Acct.Store, h :- Acct.Tm, ob :- Acct.Out, b :- Acct.Tm] Acct.Out
  (match ob
    [val (Acct.Out.next s b)]
    [(next s2 b2) (Acct.Out.next s2 (Acct.Tm.try_ b2 h))]
    [(eff op v k) (Acct.Out.eff op v (Acct.Tm.try_ k h))]
    [(exn v) (Acct.Out.next s (Acct.subst 0 v h))]
    [(stuck st) (Acct.Out.stuck st)]))

;; The handler rule (deep, by operation name, as in core): a frame handling op
;; runs its clause with the op, the argument and k' = (fn [y] (handling ops k[y] r o)).
(a/defn Acct.handleEff [s :- Acct.Store, ops :- (List Nat), r :- Acct.Tm, o :- Acct.Tm, op :- Nat, v :- Acct.Tm,
                        k :- Acct.Tm] Acct.Out
  (match (Acct.member op ops)
    [true (Acct.Out.next s (Acct.subst 0 (Acct.Tm.lit (Acct.Datum.num op))
                             (Acct.subst 0 v (Acct.subst 0 (Acct.Tm.lam (Acct.Tm.handling ops k r o)) o))))]
    [false (Acct.Out.eff op v (Acct.Tm.handling ops k r o))]))

(a/defn Acct.handlingOut [s :- Acct.Store, ops :- (List Nat), r :- Acct.Tm, o :- Acct.Tm, ob :- Acct.Out,
                          b :- Acct.Tm] Acct.Out
  (match ob
    [val (Acct.Out.next s (Acct.subst 0 b r))]
    [(next s2 b2) (Acct.Out.next s2 (Acct.Tm.handling ops b2 r o))]
    [(eff op v k) (Acct.handleEff s ops r o op v k)]
    [(exn v) (Acct.Out.exn v)]
    [(stuck st) (Acct.Out.stuck st)]))

(a/defn Acct.ev [c :- Bool, s :- Acct.Store, t :- Acct.Tm] Acct.Out
  (match t
    [(var i) (Acct.Out.stuck Acct.Stuck.scope)]
    [(lit d) Acct.Out.val]
    [(lam b) Acct.Out.val]
    [(tok i) Acct.Out.val]
    [(app f x) (Acct.seq2 (Acct.ev c s f) (Acct.ev c s x)
                          (fn [f2 :- Acct.Tm] (Acct.Tm.app f2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.app f x2))
                          (Acct.beta s f x))]
    [(let_ e b) (Acct.seq1 (Acct.ev c s e) (fn [e2 :- Acct.Tm] (Acct.Tm.let_ e2 b)) (Acct.Out.next s (Acct.subst 0 e b)))]
    [(if_ q u e) (Acct.seq1 (Acct.ev c s q) (fn [q2 :- Acct.Tm] (Acct.Tm.if_ q2 u e)) (Acct.Out.next s (Acct.pick q u e)))]
    [(take x) (Acct.seq1 (Acct.ev c s x) (fn [x2 :- Acct.Tm] (Acct.Tm.take x2)) (Acct.takeStep s x))]
    [(spend u x) (Acct.seq2 (Acct.ev c s u) (Acct.ev c s x)
                            (fn [u2 :- Acct.Tm] (Acct.Tm.spend u2 x)) (fn [x2 :- Acct.Tm] (Acct.Tm.spend u x2))
                            (Acct.spendStep c s u x))]
    [(join u v) (Acct.seq2 (Acct.ev c s u) (Acct.ev c s v)
                           (fn [u2 :- Acct.Tm] (Acct.Tm.join u2 v)) (fn [v2 :- Acct.Tm] (Acct.Tm.join u v2))
                           (Acct.joinStep c s u v))]
    [(put u) (Acct.seq1 (Acct.ev c s u) (fn [u2 :- Acct.Tm] (Acct.Tm.put u2)) (Acct.putStep c s u))]
    [(raise x) (Acct.seq1 (Acct.ev c s x) (fn [x2 :- Acct.Tm] (Acct.Tm.raise x2)) (Acct.Out.exn x))]
    [(try_ b h) (Acct.tryOut s h (Acct.ev c s b) b)]
    [(perform op x) (Acct.seq1 (Acct.ev c s x) (fn [x2 :- Acct.Tm] (Acct.Tm.perform op x2))
                               (Acct.Out.eff op x (Acct.Tm.var 0)))]
    [(handle ops b r o) (Acct.Out.next s (Acct.Tm.handling ops b r o))]
    [(handling ops b r o) (Acct.handlingOut s ops r o (Acct.ev c s b) b)]))

(a/inductive Acct.Config []
  (mk [s Acct.Store] [t Acct.Tm]))

(a/defn Acct.stepOut [o :- Acct.Out] (Option Acct.Config)
  (match o
    [(next s2 t2) (Option.some Acct.Config (Acct.Config.mk s2 t2))]
    [_ (Option.none Acct.Config)]))

;; The specification: a total step function on configurations (checked);
;; `stepU` is the same with the reuse check erased.
(a/defn Acct.step [cf :- Acct.Config] (Option Acct.Config)
  (match cf [(mk s t) (Acct.stepOut (Acct.ev true s t))]))

(a/defn Acct.stepU [cf :- Acct.Config] (Option Acct.Config)
  (match cf [(mk s t) (Acct.stepOut (Acct.ev false s t))]))
