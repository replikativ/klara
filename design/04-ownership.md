# Ownership: affine regions as checked staged rewrites

Status: the inferred mode is implemented (P6, design/PLAN.md), without its
proofs: the ownership judgment and erasure check are `klara.compile.own`
(L4.check.in-place), the recipe is `klara.own/in-place`, and
`showcases/in_place.clj` shows it on a word-count loop. The declared mode
(an explicit affine subset that programs write) is designed here and not
implemented. A first version of the declared mode was reviewed for
soundness on 2026-11-01 and failed in four ways; the design below answers
that review (last section). The earlier prototype (tag
`prototype-2026-10-31` on the `main` branch history) had a different,
hosted design, compared at the end.

## The idea

Klara stays functional. Ownership never changes what a program means: it is
a representation, a value updated in place, chosen inside a boundary where
nobody else can observe the update. The meaning of owned code is its
*erasure*, the same code with every owned operation read persistently. This
is "functional but in-place", as in Lean 4 (Ullrich and de Moura,
*Counting Immutable Beans*, 2019) and Koka (Reinking et al., *Perceus*, PLDI
2021); on the JVM there is no reference counting, so a static uniqueness
judgment plays that role.

Ownership comes from two places, with one judgment and one meaning:

- **inferred**: the investor's `klara.own/in-place` recipe rewrites an
  ordinary persistent loop into owned code, and the kernel admits it if the
  judgment holds (implemented);
- **declared**: a program writes owned code itself, in a definition marked
  `defaffine`, and the judgment is checked when it is defined; if it does
  not hold the definition is rejected with a diagnostic (planned).

## Boundaries: the memory model decides where ownership can live

A value can be owned only within a visibility boundary of the memory model
([01-lifetimes.md](01-lifetimes.md)), the same boundaries the effect classes
name (L4.facts.effect):

| boundary | who sees a write inside it | effect class of the writes it contains |
|---|---|---|
| a compiled region admitted as owned | nobody outside it | none for owned values (their erasure writes nothing); `:fresh` for arrays it allocates |
| a job (a forked world) | the job, until it is adopted | `:world` |
| the session | everyone | `:shared` |

The first is the only boundary that holds owned values. Jobs and the session
only ever see persistent values, so a fork never shares, copies or splits an
owned value, and no permission accounting across forks is needed.

**The interpreter runs the erasure.** The interpreter never holds an owned
value: `transient`, `own` and `freeze` are the identity there and the owned
operations act persistently (L0.surface.transient). Only compiled code that
the kernel admitted with the ownership judgment makes transients
(L4.check.in-place). Every way out of such code freezes (`persistent!`,
O(1)):

| way out of an owned region | what crosses |
|---|---|
| return | `persistent!` at the exits (the judgment requires it) |
| leaving to the interpreter (a failed speculation, a budget tick, L4.exec.leave) | every live local is frozen, once per transient (`prims/freeze`) |
| a call of unknown or host code, a closure, data, `throw`, `perform` | nothing: the judgment forbids a token there |
| an effect captured inside the region | nothing: compiled code performs no effects (L4.lower.subset) |

So everything that runs in the interpreter, including jobs, their
suspensions and outcomes, continuations resumed any number of times,
profile samples, lifted constants, definitions and exceptions, sees
persistent values only. A declared definition is therefore also an
obligation to compile: until it is compiled it runs its erasure, correctly
and persistently.

Host code can still make a transient through interop (`(.asTransient v)`).
It is a mutable host object like an array: `lift` refuses it, it is not
data, and jobs and the investor treat it as they treat arrays
(L2.lift.mutable).

## The owned fragment: threaded tokens

An owned value is a *token*, used linearly: every owned operation consumes
the token and returns the next one. This is Clojure's transient discipline
(whose rule Clojure users already know), not cells: a cell form such as
`(update! o f)` that changes `o` behind its name has no local erasure (in
`(do (update! o conj 3) (freeze o))` the persistent reading loses the 3).

| form | consumes | returns | erasure |
|---|---|---|---|
| `(own v)` | | a token for `v` | `v` |
| `(conj! t x)`, `(assoc! t k v)`, `(dissoc! t k)`, `(disj! t k)`, `(pop! t)` | `t` | the next token | `conj`, `assoc`, ... |
| `(get t k)`, `(nth t i)`, `(count t)`, `(contains? t k)` | nothing | a value | the same |
| `(freeze t)` (`persistent!`) | `t` | a persistent value | `t` |

A parameter can be owned:

- `^:own t`: the caller moves a token in and the function returns the next
  one (alone, or in a vector with other results); the caller's token is
  consumed by the call. Erasure: an ordinary parameter.
- `^:borrow x`: the function gets a frozen snapshot, an ordinary value. The
  caller's token is frozen for the call and owned again after it (`own` on a
  persistent value is O(1); the first writes after it copy their paths).
  Erasure: an ordinary parameter. A borrow therefore needs no lexical
  lifetime: what the callee keeps is a value.

```clojure
(defaffine add-all [^:own acc xs]          ; moves acc in, returns the next token
  (loop [i 0 acc acc]
    (if (< i (count xs)) (recur (inc i) (conj! acc (nth xs i))) acc)))

(defaffine histogram [words]             ; erasure: an ordinary persistent function
  (loop [i 0 counts (own {})]
    (if (< i (count words))
      (let [w (nth words i)]
        (recur (inc i) (assoc! counts w (inc (get counts w 0)))))  ; read, then consume
      (freeze counts))))
```

## The judgment

`WO` is a decision procedure on Core terms (`klara.compile.own` today, for
loop accumulators; the declared mode extends it). Its rules:

1. A token is made by `own`, by an owned operation from a token, or is an
   `^:own` parameter.
2. Each token is consumed at most once on every control path; reads do not
   consume it but must come before its consumption.
3. At a branch, both arms consume the same tokens; a loop threads tokens
   through `recur` at the same positions.
4. A token is never captured by a function, stored in data, compared,
   hashed, thrown, performed, or passed to a host function or a function
   that is not a declared definition with `^:own` at that position.
5. A call of a declared definition with an `^:own` parameter consumes the
   token and its result is the next token; the callee's admission is a
   premise (its generation), so redefining it retires the caller's code.
6. A region ends by freezing: at its exits every token is frozen or
   consumed.

The effect class is a property of the meaning: a definition is classified
by its erasure (L4.facts.effect). Owned writes are invisible by
construction, so they add nothing; an `^:own` callee does not write its
caller's object in the erasure either, since it returns a new value.

## How a candidate is admitted

```text
reference R ── recipe (Klara) ──> owned candidate C        (inferred)
declared definition D: R = erase(D), C = D                 (declared)

             1. WO(C)              the ownership judgment
             2. erase(C) ≡ R       the definitional checker (L4.check.*); trivial when declared
             3. lower(C)           own becomes a transient where freezing gives the value back
```

`own` lowers to a transient only for an editable collection without
metadata, and to the value itself otherwise (nil, lists, sorted
collections, values with metadata), which the owned operations then update
persistently: so `freeze ∘ own` is the identity on every value, the premise
the erasure theorem needs. Step 3 stays trusted and tested differentially,
like the rest of the backend.

## Soundness

> **Erasure.** For every closed `p` with `WO(p)`:
> `Obs(run p) = Obs(run (erase p))`,
> where `Obs` is the final value up to structural equality with class and
> metadata, the ordered effects that reach default handlers or job intents,
> the world's changes, and rule-tagged errors. Compiled code may take fewer
> steps than its erasure, so with budgets it is a refinement
> (L3.budget.steps).

What the formal semantics (`spec/formal`) needs before this can be stated:
collections; a heap of cells, each live or frozen, in `Config`; `own`, the
owned operations and `freeze` in `Tm`; a host-callback rule without replay
(true of the implementation since L3.budget.exhausted makes exhaustion inside
a host call final); `WO` defined in ansatz. The proof is a simulation: each
live cell's content is the unique occurrence of that value in the erased
term at the same point, and linearity is what keeps it unique. Then `WO`
itself, compiled from ansatz, replaces the host decision procedure.

## Klara programs do the rewriting

Recipes are Klara code over Code views ([02-compilation.md](02-compilation.md)).
**Accumulator ownership** (`klara.own/in-place`, lib/klara/own.clj) finds
loops (a self-recursive function applied where it is made, with `recur` in
tail positions) whose accumulator is only ever replaced by a persistent
update of itself (`conj`, `assoc`, `dissoc`, `disj`). It marks the
accumulator's initial value `own`, replaces the updates by their owned
versions and returns `(persistent! acc)` at the exits. It declines when
there is nothing to own.

```clojure
;; the investor considers it among other alternatives; for a test it can be forced
(jit/compile! 'app/frequencies* {:specializer own/in-place
                                 :certificate {:kind :in-place}})
```

The recipe can be wrong: if it marks a binding that escapes or is used
twice, `WO` rejects the candidate; if it changes anything else, the
definitional check of the erasure rejects it. Either way the reference keeps
running. Loop fusion and counted loops on primitive longs would be recipes
of the same kind (the latter with a premise: an argument guard or a
certificate, L4.check.certificate).

## How it ties into the memory model

- **Lifetimes.** A token is reachable only from the frames of the compiled
  region that owns it; leaving the region by any way out freezes it, so the
  roots argument (L1.retain.roots) is unchanged: after a region exits, only
  persistent values remain.
- **Bounded memory.** The point of the rewrite: a loop that builds a vector
  allocates a path-copied root per iteration in the reference and updates one
  transient in the candidate. Allocation is part of what benchmarks report.
- **Continuations.** No continuation is captured inside an owned region,
  since compiled code performs no effects, and leaving freezes. Continuations
  stay multi-shot. If compiled code ever performs effects (compiling
  everything, 07-performance.md, path step 2), capture must freeze the
  region's tokens and owned operations re-own lazily, as Perceus stops
  in-place reuse once a resumed continuation shares a value. A one-shot
  rule is not used for collections: it would add an error the erasure does
  not have, and handlers have no types to check it statically.
- **Jobs.** Jobs see only persistent values; adopting a job carries its
  world's changes and a persistent value, which the parent may own again in
  O(1).

## Arrays and other resources that cannot be frozen cheaply

A primitive array has no O(1) freeze: freezing copies. For `long[]`
accumulators (the prototype's private-accumulator family) the options are a
copy at each way out, or a run-time check that an array consumed once is
not used again, as `L3.affine.reuse` (planned) does for account tokens.
Budgets and other accounted resources are
not owned values: freezing them would mint spending rights. They are tokens
of design/10-accounting.md, which share this document's threading discipline
but keep their operations (spending is the meaning) and settle at job
boundaries.

## What the soundness review found, and the answers

The first version of the declared mode (2026-11-01) used cells, made
continuations inside a region one-shot, bound edit tokens to jobs and let
owned values cross into the interpreter. An adversarial review against the
implementation found:

| finding | answer |
|---|---|
| a suspended job resumed twice, or two resumes in parallel jobs, share an owned or fresh object | the interpreter never holds owned values; jobs and suspensions see persistent values |
| exhaustion inside a host call replayed the call, repeating its callbacks' writes (a bug of the implementation) | fixed: such an outcome is final (L3.budget.exhausted) |
| one-shot continuations change observations and cannot be checked without effect types | freeze on capture (today: no capture inside owned code, freeze on leave) |
| `own` lowered to an unguarded transient: nil, lists, sorted sets threw, metadata was lost (a bug of the implementation) | fixed: `own` becomes a transient only where freezing gives the value back |
| owned values could cross into jobs, outcomes, exceptions, `def`, `lift`, profile samples | none can: they never leave compiled code unfrozen; host transients are mutable (L2.lift.mutable) |
| the effect lattice is not an ownership judgment | effects are classified on the erasure; `WO` decides ownership |
| cell-style `update!` has no local erasure | threaded tokens |
| Clojure 1.12 transients do not check threads, and stale tokens still write | nothing relies on edit tokens: `WO` is static |
| a stored continuation can keep a region alive | no continuation holds a token |
| `(reduce + t)`, `=`, `hash` on a transient differ from the persistent value | tokens never reach host code (rule 4) |
| fractional permissions | not needed: freeze and own again cover the prototype's examples; fractions would pay only for large arrays read in parallel rounds |

## Plan

1. [x] **Views for loops** (`klara.code` covers `:recur`, self names,
   arities).
2. [x] **Owned Core in the checker**: `WO` for loop accumulators, erasure,
   admission, lowering (`klara.compile.own`, L4.check.in-place).
3. [x] **The accumulator recipe** (`klara.own/in-place`, `showcases/in_place.clj`,
   rejection cases in `test/klara/own_test.clj` and
   `test/klara/adversarial_test.clj`).
4. [x] **Fixes from the soundness review**: total lowering of `own`, final
   exhaustion inside host calls, host transients as mutable.
5. **The declared mode** (L4.check.affine, planned): `defaffine`, `^:own`
   and `^:borrow` parameters, `WO` extended by rules 1-6 above with
   diagnostics that name the rule and the place, the compile obligation at
   definition.
6. **Formal**: the store semantics, `WO` in ansatz, the erasure theorem; then
   the verified `WO` replaces the host one.
7. **Primitive arrays** as resources that cannot be frozen cheaply; budgets
   and other accounted resources are design/10-accounting.md.

## What the prototype did

The prototype (rfc/0005 and rfc/0001 at the tag) had surface forms (`own`,
`read`, `update!`, `borrow`, `move`, `freeze`, `drop!`, and `^:own`,
`^:borrow`, `^:move` parameters) on a dynamic authority store: owned cells
were one kind of authority with fractional permissions (Boyland 2003), a
fork split every authority, so a fork holding a write share was rejected and
read fractions crossed forks, and checks could run at three binding times
(every use, once per region entry, or statically with erasure). It also had
a static checker producing derivations and an inferred conversion to private
`long[]` loops, all hosted Clojure, with proofs about a separate finite
model.

This design keeps the surface idea, the declared and inferred modes with one
judgment, erasure as meaning and the requirement that ownership fit forks.
It drops the authority store and the fractions: ownership lives only inside
compiled regions, whose every way out freezes, so forks see values and the
memory model needs no second mechanism.
