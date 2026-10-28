# Klara Core: the formal semantics, readably

This document restates the semantics of Klara Core as inference rules and
tables. There are two executable sources, and this text follows both:

- **the specification**, `spec/src/klara/spec/core.clj`: a total `step`
  function over configurations, kernel-checked in
  [ansatz](https://github.com/replikativ/ansatz) together with its
  metatheory (`spec/src/klara/spec/{ws,props}.clj`, see `spec/README.md`);
- **the reference interpreter T0**, `src/klara/eval.clj`: a CEK machine
  that runs the full language (n-ary functions, worlds, dynamic handlers,
  host interop, exceptions). T0 is what the REPL and the guide run.

The specification covers a deliberately small calculus. Where T0 does
more, §9 says how it extends the rules. Where the two should agree, the 69
programs in `spec/test/klara/spec/programs.edn` are the shared corpus.
`clojure -X:spec-diff` runs every one of them through both and compares
the observations; four deliberate differences are listed in §10.

## 1. Syntax: the twelve forms

Terms use de Bruijn indices: index 0 is the innermost binder.

| Form | Surface | Spec `Tm` | T0 map (`klara.core`) |
|---|---|---|---|
| local | `x` | `var i` | `{:op :local :index i}` |
| quote | `'d`, literals | `lit d` (d ∈ nil, Bool, Int) | `{:op :quote :datum d}` (any datum) |
| fn | `(fn [x ..] e)` | `lam b` (unary) | `{:op :fn :arity n :rest? b :body t}` |
| application | `(f a ..)` | `app f x` (binary) | `{:op :app :fn t :args [..]}` |
| let | `(let [x e] b)` | `let_ e b` | `{:op :let :init t :body t}` |
| if | `(if c t e)` | `if_ c t e` | `{:op :if ..}` |
| letrec | `(letfn ..)`, `loop`, named `fn` | `letrec fb b` (one fn) | `{:op :letrec :inits [fn ..] :body t}` |
| resolve | a world name `f` | `resolve id` | `{:op :resolve :id sym}` |
| prim | `(+ a b)` … | `prim op x y`, op ∈ `+ - * = <` | `{:op :prim :name sym :args [..]}`, 44 clojure.core functions |
| perform | `(perform h :op a ..)`, `(perform :ns/op a ..)` | `perform op h x` | `{:op :perform :target t\|nil :name kw :args [..]}` |
| handle | `(handle [h {:op f .. :return r}] body)` | `handle b r o` | `{:op :handle :mode :lexical\|:dynamic :clauses {..} :return t :body t}` |
| specialize | `(specialize f a ..)` | `specialize p m` | `{:op :specialize :fn t :args [..]}` |

The spec's front end (`spec/src/klara/spec/interp.clj`) curries n-ary
functions and applications and turns a clause map `{:op clause ..}` into one
clause that dispatches on the op tag. Every other surface form is a macro
over these twelve; `doc/guide/01-core.md` lists the expansions.

Both languages have two more forms for staging, `code` (a bracket: its
body is code one level up) and `esc` (a splice back down, stuck outside
`code`). The spec has `run_` as a third form; T0 has it as the ambient
operation `:stage/run`, next to `:stage/lift` and `:stage/genlet`, which
the spec does not model. §10 gives the staging rules;
`doc/guide/05-staging.md` describes the forms for users.

The spec adds three **runtime forms** that arise only by reduction, in the
style of WebAssembly's administrative instructions:

| Form | Meaning |
|---|---|
| `fix fb` | the recursive closure created by `letrec` |
| `cap l` | the capability of handler instance `l` |
| `handling l b r o` | an installed instance `l` running body `b`, with return clause `r` and op clause `o` |

Binding structure: `lam b` binds 1 in `b`; `let_ e b` binds 1 in `b`;
`letrec fb b` binds 2 in `fb` (index 1 is the function, index 0 its
argument) and 1 in `b`; `handle b r o` binds 1 in `b` (the capability),
1 in `r` (the returned value) and 3 in `o` (index 2 the op tag, 1 the
argument, 0 the continuation).

## 2. Values, configurations, contexts

```
values       v ::= lit d | lam b | fix fb | cap l
configs      C ::= ⟨w, n, t⟩       w: world (finite map id ↦ closed value)
                                   n: next fresh handler label
                                   t: closed term
contexts     E ::= □ | E t | v E | let_ E b | if_ E t e
                 | prim op E t | prim op v E
                 | perform op E t | perform op v E
                 | specialize E t | specialize v E
                 | handling l E r o
```

Evaluation is call-by-value and left to right. `t[v/i]` substitutes the
closed value `v` for index `i` and lowers the indices above it. Only closed
values are ever substituted, so no shifting is needed.

`truthy(v)` is false for `lit nil` and `lit false` and true for every
other value (Clojure truthiness). `δ(op, d₁, d₂)` is the primitive table:
`+ - *` on integers, `<` on integers, `=` on any two datums; it is
undefined otherwise.

We write `E` is **l-free** when `E` contains no frame `handling l …`.

## 3. Reduction rules

`⟨w,n,t⟩ → ⟨w,n',t'⟩` is the graph of `step` (the relation `Step` in
`props.clj`). The rules below are read off `run1`; the names in brackets
are the functions in `core.clj` that implement them.

**Context.**
```
        ⟨w, n, t⟩ → ⟨w, n', t'⟩
  ─────────────────────────────────── (Ctx)                    [frame, seq1, seq2]
     ⟨w, n, E[t]⟩ → ⟨w, n', E[t']⟩
```

**Pure head rules** (the counter `n` is unchanged):

| Rule | Redex | Reduct | |
|---|---|---|---|
| β | `app (lam b) v` | `b[v/0]` | [beta] |
| β-fix | `app (fix fb) v` | `fb[fix fb/1][v/0]` | [beta] |
| let | `let_ v b` | `b[v/0]` | |
| if-t | `if_ v t e`, truthy(v) | `t` | [truthy] |
| if-f | `if_ v t e`, ¬truthy(v) | `e` | |
| letrec | `letrec fb b` | `b[fix fb/0]` | |
| resolve | `resolve id`, w(id) = v | `v` | [resolveResult] |
| prim | `prim op (lit d₁) (lit d₂)`, δ(op,d₁,d₂) = d | `lit d` | [primStep] |
| specialize | `specialize v₁ v₂` | `lam (app (app v₁ v₂) (var 0))` | |
| return | `handling l v r o` | `r[v/0]` | [handlingOut] |

**Handlers** (lexical instances, deep):
```
  ───────────────────────────────────────────────────────── (Handle)
   ⟨w, n, handle b r o⟩ → ⟨w, n+1, handling n b[cap n/0] r o⟩

   E is l-free        k = lam (handling l E[var 0] r o)
  ───────────────────────────────────────────────────────────────── (Op)   [handleEff]
   handling l E[perform op (cap l) v] r o  →  o[k/0][v/1][op/2]
```

`Handle` allocates a fresh label and substitutes its capability for the
handler variable. `Op` fires at the nearest instance with the performed
label: an effect aimed at another instance, or an ambient one, passes
through every `handling` frame and grows the captured context. The
continuation `k` reinstalls `handling l …` around the captured context,
which makes handlers **deep**, and `k` is an ordinary value that may be
called any number of times, which makes resumption **multi-shot** in the
reference semantics. (Fork authority, RFC 0001, will restrict multi-shot
resumption to computations whose authorities can be split; nothing
enforces this yet.)

## 4. Terminal configurations

A configuration with no step is exactly one of:

| Outcome | Shape | Meaning |
|---|---|---|
| value | `t` is a value | normal result |
| unhandled ambient op | `E[perform op (lit nil) v]` | nothing in Core handles ambient ops; the host (T0's reference handlers) does |
| unhandled instance | `E[perform op (cap l) v]`, E l-free | the capability escaped the extent of its instance |
| stuck `notFn` | `E[app v₁ v₂]`, v₁ ∈ {lit, cap} | applying a non-function |
| stuck `primType` | `E[prim op v₁ v₂]`, δ undefined | primitive outside its domain |
| stuck `badTarget` | `E[perform op v x]`, v neither `cap l` nor `lit nil` | performing on a non-capability |
| stuck `unbound id` | `E[resolve id]`, id ∉ dom w | world lookup failed |
| stuck `stage` | `esc` at level 0, `esc`/`run_` of a non-code value, an n-form at level 0 | ill-staged program (§10) |
| stuck `lift` | `cap l` or `handling` reached while building code | a capability would persist into code |
| stuck `extrusion` | `E[run_ (code u)]`, u not closed | running open code |
| scope extrusion at a splice | a splice whose code mentions a name not bound on the path to it (outcome `chk (g :: _)`) | a generated variable escaped its binder (§10) |
| stuck `scope` | a free variable reached evaluation | excluded for closed terms (§6) |

These are the **named stuck states**. `scope` is the only unnamed one, and
progress (§6) says closed configurations never reach it.

## 5. `specialize`

`specialize` is the s-m-n operation of the monoidal-computer reading:
from a program `p` and a static argument `m` it produces a program of the
remaining argument. Its **reference meaning** is partial application, the
`specialize` rule above. Any other specializer (a partial evaluator, the
fusion of S3) is an optimization that must agree with this meaning
(the s-m-n square, §8).

The law holds at values: for closed values `p`, `m`, `x`,
`app (specialize p m) x →→ app (app p m) x` in exactly two steps. It is
**false as an equation for a non-value argument**:
`((specialize p m) e)` runs `e`'s effects before `(p m)`'s, whereas
`(p m e)` runs them after.

## 6. What is proved, and what is stated

All theorems below are kernel-checked by ansatz (bundled Init only, about
30 s; `cd spec && clojure -M:test`). Since S5 they cover the staged
calculus of §10: the step function evaluates at every level. `WS n t` says all free
indices of `t` are below `n`; `WSC c` says the world's values and the term
are closed.

| Statement | Status | ansatz name |
|---|---|---|
| **Determinism**: `Step c c₁ → Step c c₂ → c₁ = c₂` | proved | `step-det` |
| **Preservation of scoping**: `Step c c₂ → WSC c → WSC c₂` | proved | `preservation`, `preservation-config` |
| **Progress modulo named stuck states**: `WSC c →` `c` is a value, steps, is an unhandled effect, is a scope extrusion at a splice, or is a named stuck state ≠ `scope` | proved | `progress`, `progress-config` |
| **Preservation of scoping across levels**: the outcome invariant holds for `ev w n t l` at every level `l` | proved | `ev-ok` |
| **run of quoted code**: for an escape-free, binder-free `t`, `run_ (code t) → t` in one step | proved | `run-quote` |
| run of quoted code with binders: `run_ (code t) →* t` | open (needs a freshness invariant for generated names) | §10 |
| **Safety**: `WSC c → Star c c₂ → Progress c₂` | proved | `safety` |
| **s-m-n for values**: `app (specialize p m) x →→ app (app p m) x`, and both reach the same terminal configurations | proved | `smn`, `smn-equiv` |
| `isVal t → run1 t = val` (simple values) | proved | `isVal-run1` |
| `run1 t = val → isVal t` | dropped in S5: code values are values but their valuehood is recursive; `Progress.value` now says `run1 t = val` | |
| s-m-n for non-value arguments | false as an equation (§5) | |
| uniqueness of labels; a capability's effect is handled by its own instance | open, not yet stated | |
| **adequacy** (operational = denotational on observations, A1–A3) | stated, not proved; no denotational model of Core yet | research note A |
| injectivity of code identity (A-O3) | stated | |
| **the authority world** (RFC 0001: no duplication of authorities, settlement exactly once, snapshot isolation) | stated as obligations AU1–AU7; not in the spec | `rfc/0001-forks-and-authority.md` |
| the three annotation contracts (hints, checked claims, approximation) | stated | `background/01-core-v2.md` §7 |

Because `step` is total, "a value, or steps, or stuck" is trivial. The
content of progress is narrower: closed terms never produce `scope`, and
every other outcome is named. One induction (`ev-ok`, the outcome
invariant `OK`, at every level) carries both progress and preservation.

## 7. Handlers and capabilities in the full language (T0)

The spec models only lexical instances. T0 runs the full design of
RFC 0002, which adds dynamic handlers for ambient operations.

| | Lexical instance | Dynamic handler |
|---|---|---|
| surface | `(handle [h {:op f .. :return r}] body)` | `(handle :dynamic {:ns/op f ..} body)` |
| handles | user operations (no namespace in `world host exn time stage auth`) | ambient operations only (`:world/*`, `:host/*`, `:exn/*`, `:time/*`, `:stage/*`; `:auth/*` are ambient but never handled by user handlers) |
| found by | the instance value: `(perform h :op ..)` searches the continuation for that instance only | dynamic search for the nearest frame with a clause for the op |
| if none | error "unhandled lexical effect" (the spec's *unhandled instance*) | the **reference handler** answers |
| why | no accidental handling by an unrelated library handler (EF4) | the platform (or a test) can reinterpret world, host and time access |

A clause receives the operation's arguments and the continuation `k`.
Not calling `k` aborts to the `handle` frame; calling it resumes with the
handler reinstalled (deep). Continuations are vectors of data frames, so
T0 permits multi-shot resumption. Since S6 a second resumption is a
fork-resume: it is refused when the continuation captured a resource or
evidence authority, and otherwise runs under a branch context that splits
the authorities it uses (RFC 0001; `doc/guide/04-forks.md`). The formal
semantics does not model authorities yet.
The well-formedness check (`klara.core/wf-errors`) rejects a lexical
handler of an ambient operation, a dynamic handler of a user operation and
an untargeted perform of a user operation.

**Reference handlers** (the ambient effects' meaning, `ev/reference-handlers`):

| Operation | Meaning |
|---|---|
| `:host/call sym args..` | call the Clojure function `sym` |
| `:host/var sym` | the value of the Clojure var `sym` |
| `:host/static cls m args..`, `:host/static-field cls f`, `:host/class sym` | Java static members and classes |
| `:world/version` | the version of the basis the code runs under |
| `:world/resolve sym` | look `sym` up in the *fiber's current* pin (sees a raise) |
| `:world/raise-basis` | move the fiber's pin to its world's newest root |
| `:world/define sym v` | publish a raw value |
| `:world/fork`, `:world/fiber`, `:world/eval-in w form`, `:world/call-in fib f args..`, `:world/invalidate [w] sym` | fork the world, create a pinned fiber, evaluate or call in a world or fiber, repair pending dependents (registered by `klara.defs`) |
| `:exn/raise ex` | uncaught: leave the machine as a host exception |

Host exceptions thrown by prims or host calls become `:exn/raise` at the
call site; `try`/`catch` is a dynamic `:exn/raise` handler. A Klara closure
called by host code (for example passed to `clojure.core/map`) runs in a
nested machine; a lexical perform from inside it cannot reach a handler
outside the host frame and raises an error at the boundary (EF5).

## 8. The commuting squares and their status

The architecture states each correctness claim as a commuting square
(`architecture.md` §8). Their status today:

| Square | Claim | Status | Evidence |
|---|---|---|---|
| Adequacy (A1) | small-step observations = observations of the weighted execution tree | stated | no denotational model yet |
| Pass correctness | each IR pass is a simulation | no IR passes exist; expander unverified | the expander is tested (X1 criteria, CodeId α-invariance); no proof |
| s-m-n (A2 ii) | `run(specialize(p,a),b) = run(p,(a,b))` | **proved** for the trivial specializer at values (spec); **tested** in T0 | `props/smn`, `eval_test/specialize-reference-meaning` |
| Guarded specialization | residual = generic under the guards; on guard failure, generic from entry without repeating effects | **tested** | R3 in `stage_test` (10 programs) and `fusion_test` (300 inputs); EF3 conjectured in general |
| Certified rewrite (instance of pass correctness) | fused = naive for every `xs : List Nat` | **proved per pipeline** in the ansatz kernel; elaborator, lowering and overflow coincidence **trusted** and tested | S3, `fusion_test` |
| Predictor soundness | γ ∘ α ⊒ id; only level 0 licenses | design | S3's shape claim is a hand-written fact checked at entry |
| Translation (approximate) | `d(⟦T e⟧, ⟦e⟧) ≤ ε(T)` | design | |
| Snapshot fork | a branch observes the pinned parent root; authorities split exactly once | snapshot part **tested**; authority part not implemented | `r4_test`, `x1_test` (iii), `world_test`; AU4 conjectured |

## 9. How T0 extends the spec

| Spec | T0 |
|---|---|
| substitution | environments and closures (CEK machine with data frames) |
| unary `lam`, binary `app` | n-ary `fn` with optional rest parameter |
| one-function `letrec` | mutually recursive `letrec` |
| datums nil/Bool/Int, 5 prims | any Clojure datum, 44 prims with clojure.core behaviour |
| world = finite map | world = versioned immutable root; code resolves against its **basis** (below) |
| ambient op = stuck | dynamic handlers, then reference handlers |
| `notFn`, `primType`, `badTarget`, `unbound` | raised as `:exn/raise` with messages "not a function", the host exception, "unhandled lexical effect", "unbound x"; unbound names are usually rejected earlier by the expander |
| — | self tail calls in constant space |
| — | the specialization cache hook on closure entry (`klara.stage`) |
| `code`, `esc`, `run_`; CSP by substitution | `code`, `esc`, `:stage/run`, `:stage/lift`, `:stage/genlet`, `with-genletrec`; CSP by `lift` (§10) |

**Bases.** A closure created at run time carries the root it was created
under and resolves world names against it (a closure is a value). World
definitions are stored as *open* closures and run under the basis of
whoever resolves them, so one definition value runs correctly in two forks
(`r4_test`). A definition whose recorded reads no longer hold in the
current root is **pending**: resolving it raises a `:pending` error rather
than running a stale expansion. `doc/guide/02-world.md` explains this with
examples.

## 10. Staging: `code`, `esc`, `run_` (S5)

The rules follow the level-indexed small-step semantics of λ○ (Davies,
*A temporal-logic approach to binding-time analysis*, LICS 1996) and
MetaML (Taha's thesis; Moggi, Taha, Benaissa, Sheard, *An idealized
MetaML*, ESOP 1999): at level 0 terms evaluate; at level `l ≥ 1` (inside
`l` brackets) nothing reduces except under `esc`. Generated binders get
fresh names, and the scope-extrusion check is BER MetaOCaml's dynamic one
(Kiselyov, *The design and implementation of BER MetaOCaml*, FLOPS 2014):
a splice is legal only while every generated variable it mentions is still
bound by a binder under construction. The relation is the graph of the
compiled `step`; `ev w n t l` is the outcome of `t` at level `l`.

**Syntax** (new `Tm` forms):
```
t ::= … | code t | esc t | run_ t                 source
        | gvar g                                  generated variable (a name)
        | nlam g b | nlet g e b                   binders opened with name g
        | nletrec g fb b | nhandle g b r o        (names g, g+1, …)
```
The n-forms bind no de Bruijn index: their bodies mention `gvar g`
instead (locally nameless). So substitution stays the closed-value
substitution of §2, and evaluation contexts never pass under a de Bruijn
binder. The fresh-name supply is the configuration's counter `n`, shared
with handler labels.

**Values at level `l ≥ 1`**: a term with no `esc` at level 1, no source
binder (every binder opened) and no `cap`/`handling`. A code value is
`code u` with `u` a level-1 value.

**Rules.** Contexts extend those of §2 by `code E` (E at level `l+1`),
`esc E` (E at level `l−1`), `run_ E`, and, at levels ≥ 1, every argument
position left to right (`app E t`, `app v E`, `if_ E t e`, `if_ v E e`, …,
`nlam g E`, `nlet g E b`, `nlet g v E`, `nhandle g b r E`, …; a handle's
op clause is built first, then its return clause, then its body, as in T0).

| Rule | Level | Redex | Reduct |
|---|---|---|---|
| open-lam | ≥ 1 | `lam b` | `nlam g b[gvar g/0]`, n ↦ n+1 |
| open-let | ≥ 1 | `let_ e b` | `nlet g e b[gvar g/0]`, n ↦ n+1 |
| open-letrec | ≥ 1 | `letrec fb b` | `nletrec g fb[gvar g/0][gvar g+1/0] b[gvar g+1/0]`, n ↦ n+2 |
| open-handle | ≥ 1 | `handle b r o` | `nhandle g b[gvar g] r[gvar g+1] o[gvar g+2, g+3, g+4]`, n ↦ n+5 |
| var-code | 0 | `gvar g` | `code (gvar g)` (a generated variable used at level 0 is its code) |
| splice | 1 | `esc (code u)` | `u`, provided the names `fnames u` are alive (below) |
| run | 0 | `run_ (code u)` | `toDB u` if it is closed, else stuck `extrusion` |

`toDB` turns every n-form back into its binder (closing the names into
indices); `wsbF` decides closedness. Persistence of level-0 values into
code (CSP) is plain substitution: a value substituted under `code` is
built like source, so an integer becomes a literal and a closure becomes
its code. A recursive closure `fix fb` is a level-≥1 value (opaque, like
T0's `#<csp fn>`); `cap l` and `handling` at level ≥ 1 are stuck `lift`.

**Liveness.** The splice rule produces the outcome `chk ns n u` rather
than `next n u`. Every n-form frame on the way to the root removes its own
names from `ns`; at the root, `chk [] n u` steps and `chk (g :: _) n u` is
the named terminal state *scope extrusion*. A name is therefore alive
exactly when its n-form is on the evaluation path, which is T0's check
(a `:blist` frame declaring the name is on the continuation). A
continuation captured inside a binder carries the n-form frame, so
resuming it makes the name alive again (program `:resume-inside-binder`).
Open code reaches a dead splice only through a side channel; in the spec
that is a handler that aborts out of a binder (`:extrusion-at-splice`).

**Not modelled.** `genlet`, `with-genletrec` and `lift` as an operation;
`:stage/*` dynamic handlers; typed staging. Let-insertion is left out:
it needs a mutable insertion point per locus, i.e. a store in the
configuration, which is not cheap here.

**Spec vs T0** (`clojure -X:spec-diff`, 69 programs, 65 agree):

| Program | Spec | T0 | Classification |
|---|---|---|---|
| `:bad-perform-target` | stuck `badTarget` | "unhandled lexical effect" | deliberate (T0 merges the two messages) |
| `:csp-code-value` | nested quotation `(+ 1 (code 1))` | stage error | deliberate: T0 refuses a code value at level 1 without `esc` |
| `:csp-closure-over-code-var` | the closure is re-read at level 1 | `lift` error | deliberate: T0 refuses; the spec's re-reading changes the closure's meaning (it returned code, its copy returns the variable) |
| `:eq-on-code` | stuck `primType` | `false` | deliberate: T0's `=` is `clojure.core/=` on all values |
