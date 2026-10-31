(ns klara.formal.core
  "The formal semantics of a fragment of Klara Core, checked by ansatz
  (spec/formal/README.md). The total function `step` is the specification;
  compiled by ansatz to Clojure it is also an executable reference
  interpreter, which test/klara/formal compares with the CEK machine.

  Ported from the earlier prototype's spec (tag prototype-2026-10-31) and
  changed to the nucleus: handlers are found by operation name (L3.perform.op)
  rather than by lexical instance, global links are late or pinned
  (L2.link.*), integers are checked 64-bit (an overflow is a named outcome,
  not an unbounded result), and `specialize` is gone.

  Representation: de Bruijn indices; staging opens binders with generated
  names (locally nameless) as in BER MetaOCaml's model of scope extrusion."
  (:require [ansatz.core :as a]))

(a/load-init!)

;; ---------------------------------------------------------------------------
;; Syntax

;; Literal data (L0.value.data, restricted): nil, booleans, integers, keywords.
;; Keywords are interned to numbers by the quoting bridge.
(a/inductive Datum []
  (nil)
  (bool [b Bool])
  (int [i Int])
  (kw [k Nat]))

(a/inductive PrimOp []
  (add) (sub) (mul) (eq) (lt))

;; Binding structure (number of de Bruijn variables each sub-term binds):
;;   lam b              b: 1
;;   let_ e b           b: 1
;;   letrec fb b        fb: 2 (1 = the function, 0 = its argument), b: 1
;;   fix fb             fb: 2, as in letrec
;;   handle ops b r o   b: 0, r: 1 (the value), o: 3 (2 = op, 1 = argument, 0 = k)
;;   handling ops b r o as handle (runtime: an installed handler frame)
;; n-forms (staging, runtime) bind no index; they carry generated names.
(a/inductive Tm []
  (var [i Nat])                                   ; local
  (lit [d Datum])                                 ; constant
  (lam [b Tm])                                    ; (fn [x] b), curried
  (app [f Tm] [x Tm])                             ; (f x), curried
  (let_ [e Tm] [b Tm])                            ; (let [x e] b)
  (if_ [c Tm] [t Tm] [e Tm])                      ; (if c t e)
  (letrec [fb Tm] [b Tm])                         ; (letfn [(f [x] fb)] b)
  (fix [fb Tm])                                   ; (fn f [x] fb), a value
  (glob [id Nat])                                 ; late link (L2.link.late)
  (pin [w Nat] [id Nat])                          ; pinned link to retained world w (L2.link.pinned)
  (prim [op PrimOp] [x Tm] [y Tm])                ; host primitive
  (perform [op Nat] [x Tm])                       ; (perform :op x)
  (handle [ops (List Nat)] [b Tm] [r Tm] [o Tm])  ; (handle {...} b)
  (handling [ops (List Nat)] [b Tm] [r Tm] [o Tm]); runtime: installed handler
  (code [t Tm])                                   ; (code t)
  (esc [t Tm])                                    ; (esc t)
  (run_ [t Tm])                                   ; (run t)
  (gvar [g Nat])                                  ; runtime: generated name
  (nlam [g Nat] [b Tm])                           ; runtime: lam whose binder is g
  (nlet [g Nat] [e Tm] [b Tm])                    ; runtime: let_ named g
  (nletrec [g Nat] [fb Tm] [b Tm])                ; runtime: letrec, g = argument, g+1 = function
  (nfix [g Nat] [fb Tm])                          ; runtime: fix, g = argument, g+1 = function
  (nhandle [g Nat] [ops (List Nat)] [b Tm] [r Tm] [o Tm])) ; runtime: g = value, g+1 = k, g+2 = arg, g+3 = op

;; A world: a finite map id -> value, as an association list.
(a/inductive World []
  (empty)
  (bind [id Nat] [v Tm] [rest World]))

;; Retained worlds for pinned links, by index.
(a/inductive Worlds []
  (none)
  (more [w World] [rest Worlds]))

;; A configuration: current world (E), retained worlds, fresh-name counter, term.
(a/inductive Config []
  (mk [w World] [ws Worlds] [fresh Nat] [t Tm]))

(a/inductive Stuck []
  (scope)              ; free variable: excluded by well-scopedness
  (notFn)              ; application of a non-function
  (primType)           ; primitive outside its domain (Klara: ClassCast, NullPointer)
  (overflow)           ; 64-bit overflow (Klara: ArithmeticException)
  (unbound [id Nat])   ; L1.resolve.unbound
  (stage)              ; L2.esc.not-code, esc outside code, n-form at level 0
  (extrusion))         ; L2.code.extrusion, L2.run.closed

;; One-step outcome.
;;   val          the term is a value
;;   next n e     steps to e with fresh counter n
;;   eff op v k   the term is E[perform op v], E does not handle op, k = E[var 0]
;;   stuck s      a named stuck state
;;   chk ns n e   a splice that steps to e provided the generated names ns are
;;                bound by an n-form between the root and the redex
(a/inductive Out []
  (val)
  (next [n Nat] [e Tm])
  (eff [op Nat] [v Tm] [k Tm])
  (stuck [s Stuck])
  (chk [ns (List Nat)] [n Nat] [e Tm]))

;; ---------------------------------------------------------------------------
;; Values, substitution, lookup

(a/defn isVal [t :- Tm] Bool
  (match t
    [(lit d) true]
    [(lam b) true]
    [(fix fb) true]
    [(code u) true]
    [_ false]))

;; Substitute the closed value v for index j, lowering indices above j.
(a/defn substVar [v :- Tm, i :- Nat, j :- Nat] Tm
  (match (Nat.beq i j)
    [true v]
    [false (match (Nat.blt j i) [true (Tm.var (- i 1))] [false (Tm.var i)])]))

(a/defn subst [j :- Nat, v :- Tm, t :- Tm] Tm
  (match t
    [(var i) (substVar v i j)]
    [(lit d) (Tm.lit d)]
    [(lam b) (Tm.lam (subst (+ j 1) v b))]
    [(app f x) (Tm.app (subst j v f) (subst j v x))]
    [(let_ e b) (Tm.let_ (subst j v e) (subst (+ j 1) v b))]
    [(if_ c u e) (Tm.if_ (subst j v c) (subst j v u) (subst j v e))]
    [(letrec fb b) (Tm.letrec (subst (+ j 2) v fb) (subst (+ j 1) v b))]
    [(fix fb) (Tm.fix (subst (+ j 2) v fb))]
    [(glob id) (Tm.glob id)]
    [(pin w id) (Tm.pin w id)]
    [(prim op x y) (Tm.prim op (subst j v x) (subst j v y))]
    [(perform op x) (Tm.perform op (subst j v x))]
    [(handle ops b r o) (Tm.handle ops (subst j v b) (subst (+ j 1) v r) (subst (+ j 3) v o))]
    [(handling ops b r o) (Tm.handling ops (subst j v b) (subst (+ j 1) v r) (subst (+ j 3) v o))]
    [(code u) (Tm.code (subst j v u))]
    [(esc u) (Tm.esc (subst j v u))]
    [(run_ u) (Tm.run_ (subst j v u))]
    [(gvar g) (Tm.gvar g)]
    [(nlam g b) (Tm.nlam g (subst j v b))]
    [(nlet g e b) (Tm.nlet g (subst j v e) (subst j v b))]
    [(nletrec g fb b) (Tm.nletrec g (subst j v fb) (subst j v b))]
    [(nfix g fb) (Tm.nfix g (subst j v fb))]
    [(nhandle g ops b r o) (Tm.nhandle g ops (subst j v b) (subst j v r) (subst j v o))]))

(a/defn lookup [w :- World, id :- Nat] (Option Tm)
  (match w
    [empty (Option.none Tm)]
    [(bind k v rest) (match (Nat.beq k id) [true (Option.some Tm v)] [false (lookup rest id)])]))

(a/defn worldAt [ws :- Worlds, i :- Nat] (Option World)
  (match ws
    [none (Option.none World)]
    [(more w rest) (match i [zero (Option.some World w)] [(succ k) (worldAt rest k)])]))

;; Pinning (L1.context.get): a value taken from retained world wi resolves its
;; own late links in wi as well.
(a/defn pinTm [wi :- Nat, t :- Tm] Tm
  (match t
    [(var i) (Tm.var i)]
    [(lit d) (Tm.lit d)]
    [(lam b) (Tm.lam (pinTm wi b))]
    [(app f x) (Tm.app (pinTm wi f) (pinTm wi x))]
    [(let_ e b) (Tm.let_ (pinTm wi e) (pinTm wi b))]
    [(if_ c u e) (Tm.if_ (pinTm wi c) (pinTm wi u) (pinTm wi e))]
    [(letrec fb b) (Tm.letrec (pinTm wi fb) (pinTm wi b))]
    [(fix fb) (Tm.fix (pinTm wi fb))]
    [(glob id) (Tm.pin wi id)]
    [(pin w id) (Tm.pin w id)]
    [(prim op x y) (Tm.prim op (pinTm wi x) (pinTm wi y))]
    [(perform op x) (Tm.perform op (pinTm wi x))]
    [(handle ops b r o) (Tm.handle ops (pinTm wi b) (pinTm wi r) (pinTm wi o))]
    [(handling ops b r o) (Tm.handling ops (pinTm wi b) (pinTm wi r) (pinTm wi o))]
    [(code u) (Tm.code (pinTm wi u))]
    [(esc u) (Tm.esc (pinTm wi u))]
    [(run_ u) (Tm.run_ (pinTm wi u))]
    [(gvar g) (Tm.gvar g)]
    [(nlam g b) (Tm.nlam g (pinTm wi b))]
    [(nlet g e b) (Tm.nlet g (pinTm wi e) (pinTm wi b))]
    [(nletrec g fb b) (Tm.nletrec g (pinTm wi fb) (pinTm wi b))]
    [(nfix g fb) (Tm.nfix g (pinTm wi fb))]
    [(nhandle g ops b r o) (Tm.nhandle g ops (pinTm wi b) (pinTm wi r) (pinTm wi o))]))

;; Clojure truthiness (L0.eval.truth).
(a/defn truthy [t :- Tm] Bool
  (match t
    [(lit d) (match d [nil false] [(bool b) b] [_ true])]
    [_ true]))

;; ---------------------------------------------------------------------------
;; Primitives on checked 64-bit integers (Clojure's + - * throw on overflow)

(a/defn maxLong [] Int (Int.ofNat 9223372036854775807))
(a/defn minLong [] Int (Int.negSucc 9223372036854775807))

(a/defn inRange [i :- Int] Bool
  (Bool.and (Bool.not (< i minLong)) (Bool.not (< maxLong i))))

(a/inductive PrimRes []
  (ok [d Datum])
  (badType)
  (overflow))

(a/defn checked [i :- Int] PrimRes
  (match (inRange i) [true (PrimRes.ok (Datum.int i))] [false PrimRes.overflow]))

(a/defn datumEq [x :- Datum, y :- Datum] Bool
  (match x
    [nil (match y [nil true] [_ false])]
    [(bool b) (match y [(bool c) (== b c)] [_ false])]
    [(int i) (match y [(int k) (== i k)] [_ false])]
    [(kw k) (match y [(kw m) (Nat.beq k m)] [_ false])]))

(a/defn intOp [op :- PrimOp, i :- Int, k :- Int] PrimRes
  (match op
    [add (checked (+ i k))]
    [sub (checked (- i k))]
    [mul (checked (* i k))]
    [eq (PrimRes.ok (Datum.bool (== i k)))]
    [lt (PrimRes.ok (Datum.bool (< i k)))]))

(a/defn primApply [op :- PrimOp, x :- Datum, y :- Datum] PrimRes
  (match op
    [eq (PrimRes.ok (Datum.bool (datumEq x y)))]
    [_ (match x
         [(int i) (match y [(int k) (intOp op i k)] [_ PrimRes.badType])]
         [_ PrimRes.badType])]))

;; ---------------------------------------------------------------------------
;; Staging helpers: generated names

(a/defn ncat [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  (match xs
    [nil ys]
    [(cons x r) (List.cons Nat x (ncat r ys))]))

(a/defn member [x :- Nat, xs :- (List Nat)] Bool
  (match xs
    [nil false]
    [(cons y r) (match (Nat.beq x y) [true true] [false (member x r)])]))

;; Remove names g .. g+k-1 (one n-form's names).
(a/defn dropRange [g :- Nat, k :- Nat, ns :- (List Nat)] (List Nat)
  (match ns
    [nil (List.nil Nat)]
    [(cons x r) (match (Bool.and (Nat.ble g x) (Nat.blt x (+ g k)))
                  [true (dropRange g k r)]
                  [false (List.cons Nat x (dropRange g k r))])]))

;; Free generated names: gvars not bound by an enclosing n-form.
(a/defn fnames [t :- Tm] (List Nat)
  (match t
    [(var i) (List.nil Nat)]
    [(lit d) (List.nil Nat)]
    [(lam b) (fnames b)]
    [(app f x) (ncat (fnames f) (fnames x))]
    [(let_ e b) (ncat (fnames e) (fnames b))]
    [(if_ c u e) (ncat (fnames c) (ncat (fnames u) (fnames e)))]
    [(letrec fb b) (ncat (fnames fb) (fnames b))]
    [(fix fb) (fnames fb)]
    [(glob id) (List.nil Nat)]
    [(pin w id) (List.nil Nat)]
    [(prim op x y) (ncat (fnames x) (fnames y))]
    [(perform op x) (fnames x)]
    [(handle ops b r o) (ncat (fnames b) (ncat (fnames r) (fnames o)))]
    [(handling ops b r o) (ncat (fnames b) (ncat (fnames r) (fnames o)))]
    [(code u) (fnames u)]
    [(esc u) (fnames u)]
    [(run_ u) (fnames u)]
    [(gvar g) (List.cons Nat g (List.nil Nat))]
    [(nlam g b) (dropRange g 1 (fnames b))]
    [(nlet g e b) (ncat (fnames e) (dropRange g 1 (fnames b)))]
    [(nletrec g fb b) (ncat (dropRange g 2 (fnames fb)) (dropRange (+ g 1) 1 (fnames b)))]
    [(nfix g fb) (dropRange g 2 (fnames fb))]
    [(nhandle g ops b r o) (ncat (fnames b) (ncat (dropRange g 1 (fnames r)) (dropRange (+ g 1) 3 (fnames o))))]))

;; Close name g into index j: gvar g becomes var j, indices at or above j move up.
(a/defn closeVar [i :- Nat, j :- Nat] Tm
  (match (Nat.blt i j) [true (Tm.var i)] [false (Tm.var (+ i 1))]))

(a/defn closeName [g :- Nat, h :- Nat, j :- Nat] Tm
  (match (Nat.beq h g) [true (Tm.var j)] [false (Tm.gvar h)]))

(a/defn closeAt [g :- Nat, j :- Nat, t :- Tm] Tm
  (match t
    [(var i) (closeVar i j)]
    [(lit d) (Tm.lit d)]
    [(lam b) (Tm.lam (closeAt g (+ j 1) b))]
    [(app f x) (Tm.app (closeAt g j f) (closeAt g j x))]
    [(let_ e b) (Tm.let_ (closeAt g j e) (closeAt g (+ j 1) b))]
    [(if_ c u e) (Tm.if_ (closeAt g j c) (closeAt g j u) (closeAt g j e))]
    [(letrec fb b) (Tm.letrec (closeAt g (+ j 2) fb) (closeAt g (+ j 1) b))]
    [(fix fb) (Tm.fix (closeAt g (+ j 2) fb))]
    [(glob id) (Tm.glob id)]
    [(pin w id) (Tm.pin w id)]
    [(prim op x y) (Tm.prim op (closeAt g j x) (closeAt g j y))]
    [(perform op x) (Tm.perform op (closeAt g j x))]
    [(handle ops b r o) (Tm.handle ops (closeAt g j b) (closeAt g (+ j 1) r) (closeAt g (+ j 3) o))]
    [(handling ops b r o) (Tm.handling ops (closeAt g j b) (closeAt g (+ j 1) r) (closeAt g (+ j 3) o))]
    [(code u) (Tm.code (closeAt g j u))]
    [(esc u) (Tm.esc (closeAt g j u))]
    [(run_ u) (Tm.run_ (closeAt g j u))]
    [(gvar h) (closeName g h j)]
    [(nlam h b) (Tm.nlam h (closeAt g j b))]
    [(nlet h e b) (Tm.nlet h (closeAt g j e) (closeAt g j b))]
    [(nletrec h fb b) (Tm.nletrec h (closeAt g j fb) (closeAt g j b))]
    [(nfix h fb) (Tm.nfix h (closeAt g j fb))]
    [(nhandle h ops b r o) (Tm.nhandle h ops (closeAt g j b) (closeAt g j r) (closeAt g j o))]))

(a/defn close [g :- Nat, t :- Tm] Tm (closeAt g 0 t))

;; Generated code back to de Bruijn form.
(a/defn toDB [t :- Tm] Tm
  (match t
    [(var i) (Tm.var i)]
    [(lit d) (Tm.lit d)]
    [(lam b) (Tm.lam (toDB b))]
    [(app f x) (Tm.app (toDB f) (toDB x))]
    [(let_ e b) (Tm.let_ (toDB e) (toDB b))]
    [(if_ c u e) (Tm.if_ (toDB c) (toDB u) (toDB e))]
    [(letrec fb b) (Tm.letrec (toDB fb) (toDB b))]
    [(fix fb) (Tm.fix (toDB fb))]
    [(glob id) (Tm.glob id)]
    [(pin w id) (Tm.pin w id)]
    [(prim op x y) (Tm.prim op (toDB x) (toDB y))]
    [(perform op x) (Tm.perform op (toDB x))]
    [(handle ops b r o) (Tm.handle ops (toDB b) (toDB r) (toDB o))]
    [(handling ops b r o) (Tm.handling ops (toDB b) (toDB r) (toDB o))]
    [(code u) (Tm.code (toDB u))]
    [(esc u) (Tm.esc (toDB u))]
    [(run_ u) (Tm.run_ (toDB u))]
    [(gvar g) (Tm.gvar g)]
    [(nlam g b) (Tm.lam (close g (toDB b)))]
    [(nlet g e b) (Tm.let_ (toDB e) (close g (toDB b)))]
    [(nletrec g fb b) (Tm.letrec (close (+ g 1) (close g (toDB fb))) (close (+ g 1) (toDB b)))]
    [(nfix g fb) (Tm.fix (close (+ g 1) (close g (toDB fb))))]
    [(nhandle g ops b r o) (Tm.handle ops (toDB b) (close g (toDB r))
                                      (close (+ g 3) (close (+ g 2) (close (+ g 1) (toDB o)))))]))

;; Closed under m binders, with no generated names or n-forms (what run_ checks).
(a/defn wsb [m :- Nat, t :- Tm] Bool
  (match t
    [(var i) (Nat.blt i m)]
    [(lit d) true]
    [(lam b) (wsb (+ m 1) b)]
    [(app f x) (Bool.and (wsb m f) (wsb m x))]
    [(let_ e b) (Bool.and (wsb m e) (wsb (+ m 1) b))]
    [(if_ c u e) (Bool.and (wsb m c) (Bool.and (wsb m u) (wsb m e)))]
    [(letrec fb b) (Bool.and (wsb (+ m 2) fb) (wsb (+ m 1) b))]
    [(fix fb) (wsb (+ m 2) fb)]
    [(glob id) true]
    [(pin w id) true]
    [(prim op x y) (Bool.and (wsb m x) (wsb m y))]
    [(perform op x) (wsb m x)]
    [(handle ops b r o) (Bool.and (wsb m b) (Bool.and (wsb (+ m 1) r) (wsb (+ m 3) o)))]
    [(handling ops b r o) (Bool.and (wsb m b) (Bool.and (wsb (+ m 1) r) (wsb (+ m 3) o)))]
    [(code u) (wsb m u)]
    [(esc u) (wsb m u)]
    [(run_ u) (wsb m u)]
    [_ false]))

;; ---------------------------------------------------------------------------
;; One step

(a/defn frame [o :- Out, fr :- (=> Tm Tm)] Out
  (match o
    [val Out.val]
    [(next n e) (Out.next n (fr e))]
    [(eff op v k) (Out.eff op v (fr k))]
    [(stuck s) (Out.stuck s)]
    [(chk ns n e) (Out.chk ns n (fr e))]))

(a/defn seq1 [o :- Out, fr :- (=> Tm Tm), done :- Out] Out
  (match o [val done] [_ (frame o fr)]))

(a/defn seq2 [o1 :- Out, o2 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), done :- Out] Out
  (match o1
    [val (match o2 [val done] [_ (frame o2 fr2)])]
    [_ (frame o1 fr1)]))

(a/defn seq3 [o1 :- Out, o2 :- Out, o3 :- Out, fr1 :- (=> Tm Tm), fr2 :- (=> Tm Tm), fr3 :- (=> Tm Tm),
              done :- Out] Out
  (match o1
    [val (seq2 o2 o3 fr2 fr3 done)]
    [_ (frame o1 fr1)]))

;; L0.eval.not-fn: keywords are functions; the fragment has no maps, so a
;; keyword applied to any value is nil.
(a/defn betaLit [n :- Nat, d :- Datum] Out
  (match d
    [(kw k) (Out.next n (Tm.lit Datum.nil))]
    [_ (Out.stuck Stuck.notFn)]))

(a/defn beta [n :- Nat, f :- Tm, x :- Tm] Out
  (match f
    [(lam b) (Out.next n (subst 0 x b))]
    [(fix fb) (Out.next n (subst 0 x (subst 1 (Tm.fix fb) fb)))]
    [(lit d) (betaLit n d)]
    [_ (Out.stuck Stuck.notFn)]))

(a/defn primResult [n :- Nat, r :- PrimRes] Out
  (match r
    [(ok d) (Out.next n (Tm.lit d))]
    [badType (Out.stuck Stuck.primType)]
    [overflow (Out.stuck Stuck.overflow)]))

(a/defn primStep [n :- Nat, op :- PrimOp, x :- Tm, y :- Tm] Out
  (match x
    [(lit d) (match y
               [(lit e) (primResult n (primApply op d e))]
               [_ (Out.stuck Stuck.primType)])]
    [_ (Out.stuck Stuck.primType)]))

;; The handler rule (deep, by operation name): a frame handling op runs its
;; clause with the op, the argument and k' = (fn [y] (handling ops k[y] r o)).
(a/defn handleEff [n :- Nat, ops :- (List Nat), r :- Tm, o :- Tm, op :- Nat, v :- Tm, k :- Tm] Out
  (match (member op ops)
    [true (Out.next n (subst 0 (Tm.lit (Datum.kw op))
                        (subst 0 v (subst 0 (Tm.lam (Tm.handling ops k r o)) o))))]
    [false (Out.eff op v (Tm.handling ops k r o))]))

(a/defn handlingOut [n :- Nat, ops :- (List Nat), r :- Tm, o :- Tm, ob :- Out, b :- Tm] Out
  (match ob
    [val (Out.next n (subst 0 b r))]
    [(next n2 b2) (Out.next n2 (Tm.handling ops b2 r o))]
    [(eff op v k) (handleEff n ops r o op v k)]
    [(stuck s) (Out.stuck s)]
    [(chk ns n2 b2) (Out.chk ns n2 (Tm.handling ops b2 r o))]))

(a/defn resolveResult [n :- Nat, id :- Nat, r :- (Option Tm)] Out
  (match r
    [none (Out.stuck (Stuck.unbound id))]
    [(some v) (Out.next n v)]))

(a/defn pinValue [n :- Nat, wi :- Nat, id :- Nat, r :- (Option Tm)] Out
  (match r
    [none (Out.stuck (Stuck.unbound id))]
    [(some v) (Out.next n (pinTm wi v))]))

(a/defn pinResult [n :- Nat, wi :- Nat, id :- Nat, w :- (Option World)] Out
  (match w
    [none (Out.stuck (Stuck.unbound id))]
    [(some wv) (pinValue n wi id (lookup wv id))]))

(a/defn atZero [l :- Nat, a :- Out, b :- Out] Out
  (match l [zero a] [(succ m) b]))

(a/defn pick [c :- Tm, u :- Tm, e :- Tm] Tm
  (match (truthy c) [true u] [false e]))

(a/defn dropOut [g :- Nat, k :- Nat, o :- Out] Out
  (match o
    [(chk ns n e) (Out.chk (dropRange g k ns) n e)]
    [_ o]))

;; Binders inside code are opened with generated names (counter n).
(a/defn openLam [n :- Nat, b :- Tm] Out
  (Out.next (+ n 1) (Tm.nlam n (subst 0 (Tm.gvar n) b))))

(a/defn openLet [n :- Nat, e :- Tm, b :- Tm] Out
  (Out.next (+ n 1) (Tm.nlet n e (subst 0 (Tm.gvar n) b))))

(a/defn openLetrec [n :- Nat, fb :- Tm, b :- Tm] Out
  (Out.next (+ n 2) (Tm.nletrec n (subst 0 (Tm.gvar (+ n 1)) (subst 0 (Tm.gvar n) fb))
                                (subst 0 (Tm.gvar (+ n 1)) b))))

(a/defn openFix [n :- Nat, fb :- Tm] Out
  (Out.next (+ n 2) (Tm.nfix n (subst 0 (Tm.gvar (+ n 1)) (subst 0 (Tm.gvar n) fb)))))

(a/defn openHandle [n :- Nat, ops :- (List Nat), b :- Tm, r :- Tm, o :- Tm] Out
  (Out.next (+ n 4) (Tm.nhandle n ops b (subst 0 (Tm.gvar n) r)
                                (subst 0 (Tm.gvar (+ n 3)) (subst 0 (Tm.gvar (+ n 2)) (subst 0 (Tm.gvar (+ n 1)) o))))))

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

(a/defn runCode [n :- Nat, c :- Tm] Out
  (match (wsb 0 c)
    [true (Out.next n c)]
    [false (Out.stuck Stuck.extrusion)]))

(a/defn runStep [n :- Nat, u :- Tm] Out
  (match u
    [(code c) (runCode n (toDB c))]
    [_ (Out.stuck Stuck.stage)]))

;; At level 0 terms evaluate; at level l >= 1 (inside l brackets) they are
;; built: children left to right, binders opened with generated names, and
;; only esc evaluates.
(a/defn ev [w :- World, ws :- Worlds, n :- Nat, l :- Nat, t :- Tm] Out
  (match t
    [(var i) (Out.stuck Stuck.scope)]
    [(lit d) Out.val]
    [(lam b) (atZero l Out.val (openLam n b))]
    [(app f x) (seq2 (ev w ws n l f) (ev w ws n l x)
                     (fn [f2 :- Tm] (Tm.app f2 x)) (fn [x2 :- Tm] (Tm.app f x2))
                     (atZero l (beta n f x) Out.val))]
    [(let_ e b) (atZero l (seq1 (ev w ws n l e) (fn [e2 :- Tm] (Tm.let_ e2 b)) (Out.next n (subst 0 e b)))
                        (openLet n e b))]
    [(if_ c u e) (atZero l (seq1 (ev w ws n l c) (fn [c2 :- Tm] (Tm.if_ c2 u e)) (Out.next n (pick c u e)))
                         (seq3 (ev w ws n l c) (ev w ws n l u) (ev w ws n l e)
                               (fn [c2 :- Tm] (Tm.if_ c2 u e)) (fn [u2 :- Tm] (Tm.if_ c u2 e))
                               (fn [e2 :- Tm] (Tm.if_ c u e2)) Out.val))]
    [(letrec fb b) (atZero l (Out.next n (subst 0 (Tm.fix fb) b)) (openLetrec n fb b))]
    [(fix fb) (atZero l Out.val (openFix n fb))]
    [(glob id) (atZero l (resolveResult n id (lookup w id)) Out.val)]
    [(pin wi id) (atZero l (pinResult n wi id (worldAt ws wi)) Out.val)]
    [(prim op x y) (seq2 (ev w ws n l x) (ev w ws n l y)
                         (fn [x2 :- Tm] (Tm.prim op x2 y)) (fn [y2 :- Tm] (Tm.prim op x y2))
                         (atZero l (primStep n op x y) Out.val))]
    [(perform op x) (seq1 (ev w ws n l x) (fn [x2 :- Tm] (Tm.perform op x2))
                          (atZero l (Out.eff op x (Tm.var 0)) Out.val))]
    [(handle ops b r o) (atZero l (Out.next n (Tm.handling ops b r o)) (openHandle n ops b r o))]
    [(handling ops b r o) (atZero l (handlingOut n ops r o (ev w ws n l b) b) (Out.stuck Stuck.stage))]
    [(code u) (frame (ev w ws n (+ l 1) u) (fn [u2 :- Tm] (Tm.code u2)))]
    [(esc u) (escOut l n u (ev w ws n (- l 1) u))]
    [(run_ u) (atZero l (seq1 (ev w ws n l u) (fn [u2 :- Tm] (Tm.run_ u2)) (runStep n u))
                      (frame (ev w ws n l u) (fn [u2 :- Tm] (Tm.run_ u2))))]
    [(gvar g) (atZero l (Out.next n (Tm.code (Tm.gvar g))) Out.val)]
    [(nlam g b) (atZero l (Out.stuck Stuck.stage)
                        (dropOut g 1 (frame (ev w ws n l b) (fn [b2 :- Tm] (Tm.nlam g b2)))))]
    [(nlet g e b) (atZero l (Out.stuck Stuck.stage)
                          (seq2 (ev w ws n l e) (dropOut g 1 (ev w ws n l b))
                                (fn [e2 :- Tm] (Tm.nlet g e2 b)) (fn [b2 :- Tm] (Tm.nlet g e b2)) Out.val))]
    [(nletrec g fb b) (atZero l (Out.stuck Stuck.stage)
                              (seq2 (dropOut g 2 (ev w ws n l fb)) (dropOut (+ g 1) 1 (ev w ws n l b))
                                    (fn [f2 :- Tm] (Tm.nletrec g f2 b)) (fn [b2 :- Tm] (Tm.nletrec g fb b2)) Out.val))]
    [(nfix g fb) (atZero l (Out.stuck Stuck.stage)
                         (dropOut g 2 (frame (ev w ws n l fb) (fn [f2 :- Tm] (Tm.nfix g f2)))))]
    [(nhandle g ops b r o) (atZero l (Out.stuck Stuck.stage)
                                   (seq3 (ev w ws n l b) (dropOut g 1 (ev w ws n l r)) (dropOut (+ g 1) 3 (ev w ws n l o))
                                         (fn [b2 :- Tm] (Tm.nhandle g ops b2 r o))
                                         (fn [r2 :- Tm] (Tm.nhandle g ops b r2 o))
                                         (fn [o2 :- Tm] (Tm.nhandle g ops b r o2)) Out.val))]))

(a/defn run1 [w :- World, ws :- Worlds, n :- Nat, t :- Tm] Out (ev w ws n 0 t))

(a/defn chkStep [w :- World, ws :- Worlds, ns :- (List Nat), n :- Nat, e :- Tm] (Option Config)
  (match ns
    [nil (Option.some Config (Config.mk w ws n e))]
    [(cons g r) (Option.none Config)]))

(a/defn stepOut [w :- World, ws :- Worlds, o :- Out] (Option Config)
  (match o
    [(next n2 t2) (Option.some Config (Config.mk w ws n2 t2))]
    [(chk ns n2 t2) (chkStep w ws ns n2 t2)]
    [_ (Option.none Config)]))

;; The specification: a total step function on configurations.
(a/defn step [c :- Config] (Option Config)
  (match c
    [(mk w ws n t) (stepOut w ws (run1 w ws n t))]))
