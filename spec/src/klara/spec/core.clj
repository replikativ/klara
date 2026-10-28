(ns klara.spec.core
  "Klara Core: syntax and small-step semantics, kernel-checked by ansatz.

  Lean-4-shaped definitions: plain inductives and structural recursion only.
  The Lean rendering of each definition is given in spec/lean/KlaraCore.lean
  (hand-written mirror, see README)."
  (:require [ansatz.core :as a]))

;; A fresh Init environment on every load: ansatz rejects redefinition.
(a/load-init!)

;; ---------------------------------------------------------------------------
;; Syntax

;; Datum literals (the V of `quote`). Clojure nil, booleans and integers.
(a/inductive Datum []
  (nil)
  (bool [b Bool])
  (int [i Int]))

(a/inductive PrimOp []
  (add) (sub) (mul) (eq) (lt))

;; Terms, de Bruijn indices. The twelve surface forms come first; `fix`, `cap`
;; and `handling` are runtime (administrative) forms that only arise by
;; reduction, in the style of Wasm's administrative instructions.
;;
;; Binding structure (number of variables each sub-term binds):
;;   lam b            b: 1 (the argument)
;;   let_ e b         b: 1
;;   letrec fb b      fb: 2 (index 1 = the function itself, index 0 = its argument)
;;                    b: 1 (the function)
;;   handle b r o     b: 1 (the capability of this handler instance)
;;                    r: 1 (the returned value)
;;                    o: 3 (index 2 = op tag, 1 = argument, 0 = continuation k)
;;   fix fb           fb: 2, as in letrec
;;   handling l b r o b: 0 (capability already substituted), r: 1, o: 3
(a/inductive Tm []
  (var [i Nat])                                   ; local
  (lit [d Datum])                                 ; (quote d)
  (lam [b Tm])                                    ; (fn [x] b)
  (app [f Tm] [x Tm])                             ; (f x)
  (let_ [e Tm] [b Tm])                            ; (let [x e] b)
  (if_ [c Tm] [t Tm] [e Tm])                      ; (if c t e)
  (letrec [fb Tm] [b Tm])                         ; (letrec [f (fn [x] fb)] b)
  (resolve [id Nat])                              ; (resolve id)
  (prim [op PrimOp] [x Tm] [y Tm])                ; (prim op x y)
  (perform [op Nat] [h Tm] [x Tm])                ; (perform h op x); h = (lit nil) => ambient
  (handle [b Tm] [r Tm] [o Tm])                   ; (handle [h] b {return r, op o})
  (specialize [p Tm] [m Tm])                      ; (specialize p m)
  (fix [fb Tm])                                   ; runtime: recursive closure
  (cap [l Nat])                                   ; runtime: capability for instance l
  (handling [l Nat] [b Tm] [r Tm] [o Tm]))        ; runtime: installed instance l

;; The global world: a finite map id -> value, as an association list.
(a/inductive World []
  (empty)
  (bind [id Nat] [v Tm] [rest World]))

;; A configuration: world, next fresh handler label, term.
(a/inductive Config []
  (mk [w World] [fresh Nat] [t Tm]))

;; Named stuck states. `scope` (a free variable reached evaluation) is the only
;; unnamed failure; progress says closed terms never produce it.
(a/inductive Stuck []
  (scope)          ; free variable: excluded by well-scopedness
  (notFn)          ; application of a non-function value
  (primType)       ; primitive applied to operands outside its domain
  (badTarget)      ; perform on a value that is neither a capability nor nil
  (unbound [id Nat])) ; resolve of an id the world does not define

;; One-step outcome of a term.
;;   val            the term is a value
;;   next n e       the term steps to e; n is the new fresh-label counter
;;   eff tg op v k  the term is E[perform tg op v] where E does not handle tg;
;;                  k = E[var 0] (the context with its hole as index 0);
;;                  tg = some l for instance l, none for an ambient op
;;   stuck s        named stuck state s
(a/inductive Out []
  (val)
  (next [n Nat] [e Tm])
  (eff [tg (Option Nat)] [op Nat] [v Tm] [k Tm])
  (stuck [s Stuck]))

;; ---------------------------------------------------------------------------
;; Values, substitution, primitives

(a/defn isVal [t :- Tm] Bool
  (match t
    [(var i) false]
    [(lit d) true]
    [(lam b) true]
    [(app f x) false]
    [(let_ e b) false]
    [(if_ c u e) false]
    [(letrec fb b) false]
    [(resolve id) false]
    [(prim op x y) false]
    [(perform op h x) false]
    [(handle b r o) false]
    [(specialize p m) false]
    [(fix fb) true]
    [(cap l) true]
    [(handling l b r o) false]))

;; Substitute the closed value v for index j, lowering the indices above j.
;; v is not shifted: the operational semantics only substitutes closed values.
;;
;; ansatz-specific: ansatz recognises structural recursion only when every
;; argument other than the matched one is passed unchanged, so the varying
;; index j is moved into the result type (substF v t : Nat -> Tm). In Lean the
;; direct `subst (j : Nat) (v : Tm) : Tm -> Tm` is structural as well.
;; Index comparisons are Bool matches on Nat.beq / Nat.blt rather than `if`
;; (which elaborates to `ite`): ansatz's `split` does not reduce an `ite` in
;; the branches, while `split_ifs` handles Bool matches (see README).
(a/defn substVar [v :- Tm, i :- Nat, j :- Nat] Tm
  (match (Nat.beq i j)
    [true v]
    [false (match (Nat.blt j i) [true (Tm.var (- i 1))] [false (Tm.var i)])]))

(a/defn substF [v :- Tm, t :- Tm] (=> Nat Tm)
  (match t
    [(var i) (fn [j :- Nat] (substVar v i j))]
    [(lit d) (fn [j :- Nat] (Tm.lit d))]
    [(lam b) (fn [j :- Nat] (Tm.lam (substF v b (+ j 1))))]
    [(app f x) (fn [j :- Nat] (Tm.app (substF v f j) (substF v x j)))]
    [(let_ e b) (fn [j :- Nat] (Tm.let_ (substF v e j) (substF v b (+ j 1))))]
    [(if_ c u e) (fn [j :- Nat] (Tm.if_ (substF v c j) (substF v u j) (substF v e j)))]
    [(letrec fb b) (fn [j :- Nat] (Tm.letrec (substF v fb (+ j 2)) (substF v b (+ j 1))))]
    [(resolve id) (fn [j :- Nat] (Tm.resolve id))]
    [(prim op x y) (fn [j :- Nat] (Tm.prim op (substF v x j) (substF v y j)))]
    [(perform op h x) (fn [j :- Nat] (Tm.perform op (substF v h j) (substF v x j)))]
    [(handle b r o) (fn [j :- Nat] (Tm.handle (substF v b (+ j 1)) (substF v r (+ j 1)) (substF v o (+ j 3))))]
    [(specialize p m) (fn [j :- Nat] (Tm.specialize (substF v p j) (substF v m j)))]
    [(fix fb) (fn [j :- Nat] (Tm.fix (substF v fb (+ j 2))))]
    [(cap l) (fn [j :- Nat] (Tm.cap l))]
    [(handling l b r o) (fn [j :- Nat] (Tm.handling l (substF v b j) (substF v r (+ j 1)) (substF v o (+ j 3))))]))

(a/defn subst [j :- Nat, v :- Tm, t :- Tm] Tm (substF v t j))

(a/defn lookup [w :- World, id :- Nat] (Option Tm)
  (match w
    [empty (Option.none Tm)]
    [(bind k v rest) (match (Nat.beq k id) [true (Option.some Tm v)] [false (lookup rest id)])]))

;; Clojure truthiness: nil and false are falsy, every other value is truthy.
(a/defn truthy [t :- Tm] Bool
  (match t
    [(lit d) (match d [nil false] [(bool b) b] [(int i) true])]
    [_ true]))

;; Integer comparisons. `(== i k)` elaborates to `decide` over DecidableEq
;; and compiles (ansatz >= 72bd88d). `(< i k)` on Int does not compile yet
;; (ansatz: "native primitive 'Int.decLt' has no Clojure runtime lowering"), and
;; a `match` on Int's constructors miscompiles (Int is a JVM number at runtime),
;; so `intLt` goes through Int.natAbs. Lean would write `decide (i < k)`.
(a/defn intEq [i :- Int, k :- Int] Bool (== i k))
;; i < k  iff  x = k - i is positive  iff  x + |x| is nonzero
(a/defn intLt [i :- Int, k :- Int] Bool
  (Nat.blt 0 (Int.natAbs (+ (- k i) (Int.ofNat (Int.natAbs (- k i)))))))

(a/defn datumEq [x :- Datum, y :- Datum] Bool
  (match x
    [nil (match y [nil true] [_ false])]
    [(bool b) (match y [(bool c) (== b c)] [_ false])]
    [(int i) (match y [(int k) (intEq i k)] [_ false])]))

;; Arithmetic on ints; `eq` is Clojure `=` on datums.
(a/defn intOp [op :- PrimOp, i :- Int, k :- Int] Datum
  (match op
    [add (Datum.int (+ i k))]
    [sub (Datum.int (- i k))]
    [mul (Datum.int (* i k))]
    [eq (Datum.bool (intEq i k))]
    [lt (Datum.bool (intLt i k))]))

(a/defn primApply [op :- PrimOp, x :- Datum, y :- Datum] (Option Datum)
  (match op
    [eq (Option.some Datum (Datum.bool (datumEq x y)))]
    [_ (match x
         [(int i) (match y
                    [(int k) (Option.some Datum (intOp op i k))]
                    [_ (Option.none Datum)])]
         [_ (Option.none Datum)])]))

;; ---------------------------------------------------------------------------
;; One step

;; Rebuild an outcome of a sub-term under the frame `fr` (an evaluation-context
;; frame given as a function of the hole): a step steps under the frame, an
;; effect grows its captured context by the frame, stuck states propagate.
(a/defn frame [o :- Out, fr :- (=> Tm Tm)] Out
  (match o
    [val Out.val]
    [(next n e) (Out.next n (fr e))]
    [(eff tg op v k) (Out.eff tg op v (fr k))]
    [(stuck s) (Out.stuck s)]))

;; Left-to-right evaluation of two sub-terms, then `done`.
(a/defn seq2 [o1 :- Out, o2 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), done :- Out] Out
  (match o1
    [val (match o2 [val done] [_ (frame o2 fr2)])]
    [_ (frame o1 fr1)]))

;; Head reductions. All arguments are values when these are reached.
(a/defn beta [n :- Nat, f :- Tm, x :- Tm] Out
  (match f
    [(lam b) (Out.next n (subst 0 x b))]
    [(fix fb) (Out.next n (subst 0 x (subst 1 (Tm.fix fb) fb)))]
    [_ (Out.stuck Stuck.notFn)]))

(a/defn primResult [n :- Nat, r :- (Option Datum)] Out
  (match r
    [none (Out.stuck Stuck.primType)]
    [(some d) (Out.next n (Tm.lit d))]))

(a/defn primStep [n :- Nat, op :- PrimOp, x :- Tm, y :- Tm] Out
  (match x
    [(lit d) (match y
               [(lit e) (primResult n (primApply op d e))]
               [_ (Out.stuck Stuck.primType)])]
    [_ (Out.stuck Stuck.primType)]))

(a/defn performStep [op :- Nat, h :- Tm, x :- Tm] Out
  (match h
    [(cap l) (Out.eff (Option.some Nat l) op x (Tm.var 0))]
    [(lit d) (match d
               [nil (Out.eff (Option.none Nat) op x (Tm.var 0))]
               [_ (Out.stuck Stuck.badTarget)])]
    [_ (Out.stuck Stuck.badTarget)]))

;; The handler rule (deep): instance l catches an effect aimed at l and runs
;; its op clause with the op tag, the argument and the continuation
;; k' = (fn [y] (handling l k[y] r o)), which reinstalls the instance.
;; Effects aimed elsewhere (other instances, ambient ops) pass through and
;; capture this frame.
(a/defn handleEff [n :- Nat, l :- Nat, r :- Tm, o :- Tm, tg :- (Option Nat), op :- Nat, v :- Tm, k :- Tm] Out
  (match tg
    [none (Out.eff tg op v (Tm.handling l k r o))]
    [(some l2) (match (Nat.beq l2 l)
                 [true (Out.next n (subst 0 (Tm.lit (Datum.int (Int.ofNat op)))
                                     (subst 0 v (subst 0 (Tm.lam (Tm.handling l k r o)) o))))]
                 [false (Out.eff tg op v (Tm.handling l k r o))])]))

(a/defn seq1 [o :- Out, fr :- (=> Tm Tm), done :- Out] Out
  (match o
    [val done]
    [_ (frame o fr)]))

;; The handling frame: return clause on a value, handler rule on an effect.
(a/defn handlingOut [n :- Nat, l :- Nat, b :- Tm, r :- Tm, o :- Tm, ob :- Out] Out
  (match ob
    [val (Out.next n (subst 0 b r))]
    [(next n2 b2) (Out.next n2 (Tm.handling l b2 r o))]
    [(eff tg op v k) (handleEff n l r o tg op v k)]
    [(stuck s) (Out.stuck s)]))

(a/defn resolveResult [n :- Nat, id :- Nat, r :- (Option Tm)] Out
  (match r
    [none (Out.stuck (Stuck.unbound id))]
    [(some v) (Out.next n v)]))

;; ansatz-specific: a recursive call may not be a `match` scrutinee (ansatz then
;; fails to see the recursion as structural), so sub-term outcomes are passed
;; to the helpers seq1/seq2/handlingOut as arguments.
(a/defn run1 [w :- World, n :- Nat, t :- Tm] Out
  (match t
    [(var i) (Out.stuck Stuck.scope)]
    [(lit d) Out.val]
    [(lam b) Out.val]
    [(app f x) (seq2 (run1 w n f) (run1 w n x)
                     (fn [f2 :- Tm] (Tm.app f2 x)) (fn [x2 :- Tm] (Tm.app f x2))
                     (beta n f x))]
    [(let_ e b) (seq1 (run1 w n e) (fn [e2 :- Tm] (Tm.let_ e2 b))
                      (Out.next n (subst 0 e b)))]
    [(if_ c u e) (seq1 (run1 w n c) (fn [c2 :- Tm] (Tm.if_ c2 u e))
                       (Out.next n (match (truthy c) [true u] [false e])))]
    [(letrec fb b) (Out.next n (subst 0 (Tm.fix fb) b))]
    [(resolve id) (resolveResult n id (lookup w id))]
    [(prim op x y) (seq2 (run1 w n x) (run1 w n y)
                         (fn [x2 :- Tm] (Tm.prim op x2 y)) (fn [y2 :- Tm] (Tm.prim op x y2))
                         (primStep n op x y))]
    [(perform op h x) (seq2 (run1 w n h) (run1 w n x)
                            (fn [h2 :- Tm] (Tm.perform op h2 x)) (fn [x2 :- Tm] (Tm.perform op h x2))
                            (performStep op h x))]
    [(handle b r o) (Out.next (+ n 1) (Tm.handling n (subst 0 (Tm.cap n) b) r o))]
    [(specialize p m) (seq2 (run1 w n p) (run1 w n m)
                            (fn [p2 :- Tm] (Tm.specialize p2 m)) (fn [m2 :- Tm] (Tm.specialize p m2))
                            (Out.next n (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0)))))]
    [(fix fb) Out.val]
    [(cap l) Out.val]
    [(handling l b r o) (handlingOut n l b r o (run1 w n b))]))

;; The interpreter-facing step function on configurations: total.
(a/defn stepOut [w :- World, o :- Out] (Option Config)
  (match o
    [(next n2 t2) (Option.some Config (Config.mk w n2 t2))]
    [_ (Option.none Config)]))

(a/defn step [c :- Config] (Option Config)
  (match c
    [(mk w n t) (stepOut w (run1 w n t))]))
