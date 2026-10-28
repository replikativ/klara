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
;;
;; Staging (S5). `code t` holds t one level up, `esc t` goes one level down,
;; `run_ t` runs closed code. Building code at level >= 1 OPENS each binder
;; with a fresh name (a `gvar`) taken from the configuration's counter, in
;; the locally-nameless style: `lam b` at level >= 1 becomes
;; `nlam g b[gvar g/0]`. The n-forms bind no de Bruijn index (their bodies
;; mention the names instead), so substitution of closed values stays
;; capture-free and evaluation contexts never go under a de Bruijn binder.
;; `run_` converts the n-forms back (`toDB`) and checks closedness.
;;   code t, esc t, run_ t, gvar g      bind nothing
;;   nlam g b, nlet g e b, nletrec g fb b, nhandle g b r o   bind nothing
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
  (handling [l Nat] [b Tm] [r Tm] [o Tm])         ; runtime: installed instance l
  ;; staging (S5)
  (code [t Tm])                                   ; (code t): bracket, t is one level up
  (esc [t Tm])                                    ; (esc t): splice, one level down
  (run_ [t Tm])                                   ; (run t): run closed code
  (gvar [g Nat])                                  ; runtime: generated variable (a name)
  (nlam [g Nat] [b Tm])                           ; runtime: lam whose binder was named g
  (nlet [g Nat] [e Tm] [b Tm])                    ; runtime: let_ named g
  (nletrec [g Nat] [fb Tm] [b Tm])                ; runtime: letrec named g (arg), g+1 (fn)
  (nhandle [g Nat] [b Tm] [r Tm] [o Tm]))         ; runtime: handle named g (cap), g+1 (ret),
                                                  ;   g+2 (k), g+3 (arg), g+4 (op tag)

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
  (unbound [id Nat])  ; resolve of an id the world does not define
  (stage)             ; esc outside code, esc/run of a non-code value, n-form at level 0
  (lift)              ; a capability or installed handler would persist into code
  (extrusion))        ; run of open code (a free generated name)

;; One-step outcome of a term.
;;   val            the term is a value
;;   next n e       the term steps to e; n is the new fresh-label counter
;;   eff tg op v k  the term is E[perform tg op v] where E does not handle tg;
;;                  k = E[var 0] (the context with its hole as index 0);
;;                  tg = some l for instance l, none for an ambient op
;;   stuck s        named stuck state s
;;   chk ns n e     a splice: the term steps to e PROVIDED the generated
;;                  names ns are alive, i.e. bound by an n-form on the path
;;                  from the root to the redex (BER MetaOCaml's dynamic
;;                  scope-extrusion check). Each n-form frame removes its own
;;                  names; at the top, chk [] steps and chk (g :: _) is the
;;                  named stuck state "scope extrusion".
(a/inductive Out []
  (val)
  (next [n Nat] [e Tm])
  (eff [tg (Option Nat)] [op Nat] [v Tm] [k Tm])
  (stuck [s Stuck])
  (chk [ns (List Nat)] [n Nat] [e Tm]))

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
    [(handling l b r o) false]
    [_ false]))

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
    [(handling l b r o) (fn [j :- Nat] (Tm.handling l (substF v b j) (substF v r (+ j 1)) (substF v o (+ j 3))))]
    [(code u) (fn [j :- Nat] (Tm.code (substF v u j)))]
    [(esc u) (fn [j :- Nat] (Tm.esc (substF v u j)))]
    [(run_ u) (fn [j :- Nat] (Tm.run_ (substF v u j)))]
    [(gvar g) (fn [j :- Nat] (Tm.gvar g))]
    [(nlam g b) (fn [j :- Nat] (Tm.nlam g (substF v b j)))]
    [(nlet g e b) (fn [j :- Nat] (Tm.nlet g (substF v e j) (substF v b j)))]
    [(nletrec g fb b) (fn [j :- Nat] (Tm.nletrec g (substF v fb j) (substF v b j)))]
    [(nhandle g b r o) (fn [j :- Nat] (Tm.nhandle g (substF v b j) (substF v r j) (substF v o j)))]))

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
;; Staging helpers: generated names, closing, closedness

;; Lists of generated names (own definitions keep the proofs independent of
;; the List library).
(a/defn ncat [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  (match xs
    [nil ys]
    [(cons x r) (List.cons Nat x (ncat r ys))]))

;; Remove the names g, g+1, .., g+k-1 (one n-form's names) from a list.
(a/defn dropRange [g :- Nat, k :- Nat, ns :- (List Nat)] (List Nat)
  (match ns
    [nil (List.nil Nat)]
    [(cons x r) (match (Bool.and (Nat.ble g x) (Nat.blt x (+ g k)))
                  [true (dropRange g k r)]
                  [false (List.cons Nat x (dropRange g k r))])]))

;; Free generated names of a term: gvars not bound by an enclosing n-form.
(a/defn fnames [t :- Tm] (List Nat)
  (match t
    [(var i) (List.nil Nat)]
    [(lit d) (List.nil Nat)]
    [(lam b) (fnames b)]
    [(app f x) (ncat (fnames f) (fnames x))]
    [(let_ e b) (ncat (fnames e) (fnames b))]
    [(if_ c u e) (ncat (fnames c) (ncat (fnames u) (fnames e)))]
    [(letrec fb b) (ncat (fnames fb) (fnames b))]
    [(resolve id) (List.nil Nat)]
    [(prim op x y) (ncat (fnames x) (fnames y))]
    [(perform op h x) (ncat (fnames h) (fnames x))]
    [(handle b r o) (ncat (fnames b) (ncat (fnames r) (fnames o)))]
    [(specialize p m) (ncat (fnames p) (fnames m))]
    [(fix fb) (fnames fb)]
    [(cap l) (List.nil Nat)]
    [(handling l b r o) (ncat (fnames b) (ncat (fnames r) (fnames o)))]
    [(code u) (fnames u)]
    [(esc u) (fnames u)]
    [(run_ u) (fnames u)]
    [(gvar g) (List.cons Nat g (List.nil Nat))]
    [(nlam g b) (dropRange g 1 (fnames b))]
    [(nlet g e b) (dropRange g 1 (ncat (fnames e) (fnames b)))]
    [(nletrec g fb b) (dropRange g 2 (ncat (fnames fb) (fnames b)))]
    [(nhandle g b r o) (dropRange g 5 (ncat (fnames b) (ncat (fnames r) (fnames o))))]))

;; Close name g into index j (locally-nameless `close`): gvar g becomes var j,
;; indices at or above j move up by one. The depth j is in the result type
;; for the same ansatz reason as substF.
(a/defn closeVar [i :- Nat, j :- Nat] Tm
  (match (Nat.blt i j) [true (Tm.var i)] [false (Tm.var (+ i 1))]))

(a/defn closeName [g :- Nat, h :- Nat, j :- Nat] Tm
  (match (Nat.beq h g) [true (Tm.var j)] [false (Tm.gvar h)]))

(a/defn closeF [g :- Nat, t :- Tm] (=> Nat Tm)
  (match t
    [(var i) (fn [j :- Nat] (closeVar i j))]
    [(lit d) (fn [j :- Nat] (Tm.lit d))]
    [(lam b) (fn [j :- Nat] (Tm.lam (closeF g b (+ j 1))))]
    [(app f x) (fn [j :- Nat] (Tm.app (closeF g f j) (closeF g x j)))]
    [(let_ e b) (fn [j :- Nat] (Tm.let_ (closeF g e j) (closeF g b (+ j 1))))]
    [(if_ c u e) (fn [j :- Nat] (Tm.if_ (closeF g c j) (closeF g u j) (closeF g e j)))]
    [(letrec fb b) (fn [j :- Nat] (Tm.letrec (closeF g fb (+ j 2)) (closeF g b (+ j 1))))]
    [(resolve id) (fn [j :- Nat] (Tm.resolve id))]
    [(prim op x y) (fn [j :- Nat] (Tm.prim op (closeF g x j) (closeF g y j)))]
    [(perform op h x) (fn [j :- Nat] (Tm.perform op (closeF g h j) (closeF g x j)))]
    [(handle b r o) (fn [j :- Nat] (Tm.handle (closeF g b (+ j 1)) (closeF g r (+ j 1)) (closeF g o (+ j 3))))]
    [(specialize p m) (fn [j :- Nat] (Tm.specialize (closeF g p j) (closeF g m j)))]
    [(fix fb) (fn [j :- Nat] (Tm.fix (closeF g fb (+ j 2))))]
    [(cap l) (fn [j :- Nat] (Tm.cap l))]
    [(handling l b r o) (fn [j :- Nat] (Tm.handling l (closeF g b j) (closeF g r (+ j 1)) (closeF g o (+ j 3))))]
    [(code u) (fn [j :- Nat] (Tm.code (closeF g u j)))]
    [(esc u) (fn [j :- Nat] (Tm.esc (closeF g u j)))]
    [(run_ u) (fn [j :- Nat] (Tm.run_ (closeF g u j)))]
    [(gvar h) (fn [j :- Nat] (closeName g h j))]
    [(nlam h b) (fn [j :- Nat] (Tm.nlam h (closeF g b j)))]
    [(nlet h e b) (fn [j :- Nat] (Tm.nlet h (closeF g e j) (closeF g b j)))]
    [(nletrec h fb b) (fn [j :- Nat] (Tm.nletrec h (closeF g fb j) (closeF g b j)))]
    [(nhandle h b r o) (fn [j :- Nat] (Tm.nhandle h (closeF g b j) (closeF g r j) (closeF g o j)))]))

(a/defn close [g :- Nat, t :- Tm] Tm (closeF g t 0))

;; Generated code back to de Bruijn form: every n-form becomes its binder
;; again (what S4's `s->core` does for T0's named s-terms).
(a/defn toDB [t :- Tm] Tm
  (match t
    [(var i) (Tm.var i)]
    [(lit d) (Tm.lit d)]
    [(lam b) (Tm.lam (toDB b))]
    [(app f x) (Tm.app (toDB f) (toDB x))]
    [(let_ e b) (Tm.let_ (toDB e) (toDB b))]
    [(if_ c u e) (Tm.if_ (toDB c) (toDB u) (toDB e))]
    [(letrec fb b) (Tm.letrec (toDB fb) (toDB b))]
    [(resolve id) (Tm.resolve id)]
    [(prim op x y) (Tm.prim op (toDB x) (toDB y))]
    [(perform op h x) (Tm.perform op (toDB h) (toDB x))]
    [(handle b r o) (Tm.handle (toDB b) (toDB r) (toDB o))]
    [(specialize p m) (Tm.specialize (toDB p) (toDB m))]
    [(fix fb) (Tm.fix (toDB fb))]
    [(cap l) (Tm.cap l)]
    [(handling l b r o) (Tm.handling l (toDB b) (toDB r) (toDB o))]
    [(code u) (Tm.code (toDB u))]
    [(esc u) (Tm.esc (toDB u))]
    [(run_ u) (Tm.run_ (toDB u))]
    [(gvar g) (Tm.gvar g)]
    [(nlam g b) (Tm.lam (close g (toDB b)))]
    [(nlet g e b) (Tm.let_ (toDB e) (close g (toDB b)))]
    [(nletrec g fb b) (Tm.letrec (close g (close (+ g 1) (toDB fb))) (close (+ g 1) (toDB b)))]
    [(nhandle g b r o) (Tm.handle (close g (toDB b)) (close (+ g 1) (toDB r))
                                  (close (+ g 2) (close (+ g 3) (close (+ g 4) (toDB o)))))]))

;; Decision procedure for "de Bruijn term closed under m binders, with no
;; generated names and no n-forms": the check `run_` makes (sound: wsbF-WS).
(a/defn wsbF [t :- Tm] (=> Nat Bool)
  (match t
    [(var i) (fn [m :- Nat] (Nat.blt i m))]
    [(lit d) (fn [m :- Nat] true)]
    [(lam b) (fn [m :- Nat] (wsbF b (+ m 1)))]
    [(app f x) (fn [m :- Nat] (Bool.and (wsbF f m) (wsbF x m)))]
    [(let_ e b) (fn [m :- Nat] (Bool.and (wsbF e m) (wsbF b (+ m 1))))]
    [(if_ c u e) (fn [m :- Nat] (Bool.and (wsbF c m) (Bool.and (wsbF u m) (wsbF e m))))]
    [(letrec fb b) (fn [m :- Nat] (Bool.and (wsbF fb (+ m 2)) (wsbF b (+ m 1))))]
    [(resolve id) (fn [m :- Nat] true)]
    [(prim op x y) (fn [m :- Nat] (Bool.and (wsbF x m) (wsbF y m)))]
    [(perform op h x) (fn [m :- Nat] (Bool.and (wsbF h m) (wsbF x m)))]
    [(handle b r o) (fn [m :- Nat] (Bool.and (wsbF b (+ m 1)) (Bool.and (wsbF r (+ m 1)) (wsbF o (+ m 3)))))]
    [(specialize p q) (fn [m :- Nat] (Bool.and (wsbF p m) (wsbF q m)))]
    [(fix fb) (fn [m :- Nat] (wsbF fb (+ m 2)))]
    [(cap l) (fn [m :- Nat] true)]
    [(handling l b r o) (fn [m :- Nat] (Bool.and (wsbF b m) (Bool.and (wsbF r (+ m 1)) (wsbF o (+ m 3)))))]
    [(code u) (fn [m :- Nat] (wsbF u m))]
    [(esc u) (fn [m :- Nat] (wsbF u m))]
    [(run_ u) (fn [m :- Nat] (wsbF u m))]
    [(gvar g) (fn [m :- Nat] false)]
    [(nlam g b) (fn [m :- Nat] false)]
    [(nlet g e b) (fn [m :- Nat] false)]
    [(nletrec g fb b) (fn [m :- Nat] false)]
    [(nhandle g b r o) (fn [m :- Nat] false)]))

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
    [(stuck s) (Out.stuck s)]
    [(chk ns n e) (Out.chk ns n (fr e))]))

;; Left-to-right evaluation of two sub-terms, then `done`.
(a/defn seq2 [o1 :- Out, o2 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), done :- Out] Out
  (match o1
    [val (match o2 [val done] [_ (frame o2 fr2)])]
    [_ (frame o1 fr1)]))

;; ... of three sub-terms.
(a/defn seq3 [o1 :- Out, o2 :- Out, o3 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), fr3 :- (=> Tm Tm),
              done :- Out] Out
  (match o1
    [val (seq2 o2 o3 fr2 fr3 done)]
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
    [(stuck s) (Out.stuck s)]
    [(chk ns n2 b2) (Out.chk ns n2 (Tm.handling l b2 r o))]))

(a/defn resolveResult [n :- Nat, id :- Nat, r :- (Option Tm)] Out
  (match r
    [none (Out.stuck (Stuck.unbound id))]
    [(some v) (Out.next n v)]))

;; Level dispatch: `a` at level 0 (evaluation), `b` at level >= 1 (building).
(a/defn atZero [l :- Nat, a :- Out, b :- Out] Out
  (match l
    [zero a]
    [(succ m) b]))

(a/defn pick [c :- Tm, u :- Tm, e :- Tm] Tm
  (match (truthy c) [true u] [false e]))

;; An n-form frame: names g .. g+k-1 are alive below it.
(a/defn dropOut [g :- Nat, k :- Nat, o :- Out] Out
  (match o
    [(chk ns n e) (Out.chk (dropRange g k ns) n e)]
    [_ o]))

;; Binders at level >= 1 are opened with fresh names (counter n).
(a/defn openLam [n :- Nat, b :- Tm] Out
  (Out.next (+ n 1) (Tm.nlam n (subst 0 (Tm.gvar n) b))))

(a/defn openLet [n :- Nat, e :- Tm, b :- Tm] Out
  (Out.next (+ n 1) (Tm.nlet n e (subst 0 (Tm.gvar n) b))))

;; fb: index 0 = the argument (name n), index 1 = the function (name n+1).
(a/defn openLetrec [n :- Nat, fb :- Tm, b :- Tm] Out
  (Out.next (+ n 2) (Tm.nletrec n (subst 0 (Tm.gvar (+ n 1)) (subst 0 (Tm.gvar n) fb))
                                (subst 0 (Tm.gvar (+ n 1)) b))))

;; b: cap (n); r: returned value (n+1); o: k (n+2), arg (n+3), op tag (n+4).
(a/defn openHandle [n :- Nat, b :- Tm, r :- Tm, o :- Tm] Out
  (Out.next (+ n 5) (Tm.nhandle n (subst 0 (Tm.gvar n) b) (subst 0 (Tm.gvar (+ n 1)) r)
                                (subst 0 (Tm.gvar (+ n 4)) (subst 0 (Tm.gvar (+ n 3)) (subst 0 (Tm.gvar (+ n 2)) o))))))

;; esc at level l: stuck at 0; at 1 evaluate the body (level 0) and splice;
;; at >= 2 build the body one level down.
(a/defn splice [n :- Nat, u :- Tm] Out
  (match u
    [(code c) (Out.chk (fnames c) n c)]
    [_ (Out.stuck Stuck.stage)]))

(a/defn escAt [m :- Nat, n :- Nat, u :- Tm, o :- Out] Out
  (match m
    [zero (seq1 o (fn [u2 :- Tm] (Tm.esc u2)) (splice n u))]
    [(succ k) (frame o (fn [u2 :- Tm] (Tm.esc u2)))]))

(a/defn escOut [l :- Nat, n :- Nat, u :- Tm, o :- Out] Out
  (match l
    [zero (Out.stuck Stuck.stage)]
    [(succ m) (escAt m n u o)]))

;; run: the code's term, converted to de Bruijn form, must be closed.
(a/defn runCode [n :- Nat, c :- Tm] Out
  (match (wsbF c 0)
    [true (Out.next n c)]
    [false (Out.stuck Stuck.extrusion)]))

(a/defn runStep [n :- Nat, u :- Tm] Out
  (match u
    [(code c) (runCode n (toDB c))]
    [_ (Out.stuck Stuck.stage)]))

;; ansatz-specific: a recursive call may not be a `match` scrutinee (ansatz then
;; fails to see the recursion as structural), so sub-term outcomes are passed
;; to the helpers as arguments. The level l is in the result type
;; (ev w n t : Nat -> Out) because it varies between recursive calls
;; (code: l+1, esc: l-1), the same workaround as substF.
;;
;; At level 0 this is the S2 evaluator plus code/esc/run_/gvar. At level
;; l >= 1 (inside l brackets) nothing reduces except under esc: compound
;; terms build their children left to right, binders are opened with fresh
;; names, and a sub-term is a value when it is fully built.
(a/defn ev [w :- World, n :- Nat, t :- Tm] (=> Nat Out)
  (match t
    [(var i) (fn [l :- Nat] (Out.stuck Stuck.scope))]
    [(lit d) (fn [l :- Nat] Out.val)]
    [(lam b) (fn [l :- Nat] (atZero l Out.val (openLam n b)))]
    [(app f x) (fn [l :- Nat] (seq2 (ev w n f l) (ev w n x l)
                                    (fn [f2 :- Tm] (Tm.app f2 x)) (fn [x2 :- Tm] (Tm.app f x2))
                                    (atZero l (beta n f x) Out.val)))]
    [(let_ e b) (fn [l :- Nat] (atZero l (seq1 (ev w n e l) (fn [e2 :- Tm] (Tm.let_ e2 b))
                                               (Out.next n (subst 0 e b)))
                                       (openLet n e b)))]
    [(if_ c u e) (fn [l :- Nat] (atZero l (seq1 (ev w n c l) (fn [c2 :- Tm] (Tm.if_ c2 u e))
                                                (Out.next n (pick c u e)))
                                        (seq3 (ev w n c l) (ev w n u l) (ev w n e l)
                                              (fn [c2 :- Tm] (Tm.if_ c2 u e)) (fn [u2 :- Tm] (Tm.if_ c u2 e))
                                              (fn [e2 :- Tm] (Tm.if_ c u e2)) Out.val)))]
    [(letrec fb b) (fn [l :- Nat] (atZero l (Out.next n (subst 0 (Tm.fix fb) b)) (openLetrec n fb b)))]
    [(resolve id) (fn [l :- Nat] (atZero l (resolveResult n id (lookup w id)) Out.val))]
    [(prim op x y) (fn [l :- Nat] (seq2 (ev w n x l) (ev w n y l)
                                        (fn [x2 :- Tm] (Tm.prim op x2 y)) (fn [y2 :- Tm] (Tm.prim op x y2))
                                        (atZero l (primStep n op x y) Out.val)))]
    [(perform op h x) (fn [l :- Nat] (seq2 (ev w n h l) (ev w n x l)
                                           (fn [h2 :- Tm] (Tm.perform op h2 x)) (fn [x2 :- Tm] (Tm.perform op h x2))
                                           (atZero l (performStep op h x) Out.val)))]
    [(handle b r o) (fn [l :- Nat] (atZero l (Out.next (+ n 1) (Tm.handling n (subst 0 (Tm.cap n) b) r o))
                                           (openHandle n b r o)))]
    [(specialize p m) (fn [l :- Nat] (seq2 (ev w n p l) (ev w n m l)
                                           (fn [p2 :- Tm] (Tm.specialize p2 m)) (fn [m2 :- Tm] (Tm.specialize p m2))
                                           (atZero l (Out.next n (Tm.lam (Tm.app (Tm.app p m) (Tm.var 0)))) Out.val)))]
    [(fix fb) (fn [l :- Nat] Out.val)]
    [(cap c) (fn [l :- Nat] (atZero l Out.val (Out.stuck Stuck.lift)))]
    [(handling c b r o) (fn [l :- Nat] (atZero l (handlingOut n c b r o (ev w n b l)) (Out.stuck Stuck.lift)))]
    [(code u) (fn [l :- Nat] (frame (ev w n u (+ l 1)) (fn [u2 :- Tm] (Tm.code u2))))]
    [(esc u) (fn [l :- Nat] (escOut l n u (ev w n u (- l 1))))]
    [(run_ u) (fn [l :- Nat] (atZero l (seq1 (ev w n u l) (fn [u2 :- Tm] (Tm.run_ u2)) (runStep n u))
                                     (frame (ev w n u l) (fn [u2 :- Tm] (Tm.run_ u2)))))]
    [(gvar g) (fn [l :- Nat] (atZero l (Out.next n (Tm.code (Tm.gvar g))) Out.val))]
    [(nlam g b) (fn [l :- Nat] (atZero l (Out.stuck Stuck.stage)
                                       (dropOut g 1 (frame (ev w n b l) (fn [b2 :- Tm] (Tm.nlam g b2))))))]
    [(nlet g e b) (fn [l :- Nat] (atZero l (Out.stuck Stuck.stage)
                                         (dropOut g 1 (seq2 (ev w n e l) (ev w n b l)
                                                            (fn [e2 :- Tm] (Tm.nlet g e2 b))
                                                            (fn [b2 :- Tm] (Tm.nlet g e b2)) Out.val))))]
    [(nletrec g fb b) (fn [l :- Nat] (atZero l (Out.stuck Stuck.stage)
                                             (dropOut g 2 (seq2 (ev w n fb l) (ev w n b l)
                                                                (fn [f2 :- Tm] (Tm.nletrec g f2 b))
                                                                (fn [b2 :- Tm] (Tm.nletrec g fb b2)) Out.val))))]
    ;; T0 builds a handle's clauses, then its return clause, then its body
    [(nhandle g b r o) (fn [l :- Nat] (atZero l (Out.stuck Stuck.stage)
                                              (dropOut g 5 (seq3 (ev w n o l) (ev w n r l) (ev w n b l)
                                                                 (fn [o2 :- Tm] (Tm.nhandle g b r o2))
                                                                 (fn [r2 :- Tm] (Tm.nhandle g b r2 o))
                                                                 (fn [b2 :- Tm] (Tm.nhandle g b2 r o)) Out.val))))]))

;; Level 0: the outcome of a top-level term.
(a/defn run1 [w :- World, n :- Nat, t :- Tm] Out (ev w n t 0))

;; The interpreter-facing step function on configurations: total. A splice
;; whose names are all alive steps; otherwise the configuration is stuck
;; (scope extrusion).
(a/defn chkStep [w :- World, ns :- (List Nat), n :- Nat, e :- Tm] (Option Config)
  (match ns
    [nil (Option.some Config (Config.mk w n e))]
    [(cons g r) (Option.none Config)]))

(a/defn stepOut [w :- World, o :- Out] (Option Config)
  (match o
    [(next n2 t2) (Option.some Config (Config.mk w n2 t2))]
    [(chk ns n2 t2) (chkStep w ns n2 t2)]
    [_ (Option.none Config)]))

(a/defn step [c :- Config] (Option Config)
  (match c
    [(mk w n t) (stepOut w (run1 w n t))]))
