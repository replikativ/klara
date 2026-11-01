# The staged JIT: one interpreter, two binding times

Status: implemented through P7 step 6 (the staged interpreter is
`jit/default`); the proof (step 7) is later. It replaced the default
specializer's tree rewrites (`speculate-branches`, `specialize-known-calls`,
`inline-calls`) and the separate partial evaluator
(`klara.compiler.recipes/inline`) with the design of
[06-speculation.md](06-speculation.md) §4: one interpreter for Core, written
in Klara, that computes what is known and generates code for the rest.

## Why

Today's default specializer reads the reference as a tree and patches it:
it looks at an `if` and its branch counts and wraps it in a speculation, it
looks at a call and inlines the callee's body. Three problems follow from
that shape:

- **It sidesteps hygiene.** Patching keeps the reference's binders and
  names, and its subterms are open (their locals are bound by the
  reference, not by a code template under construction), so splicing them
  with `code`/`esc` would trip the extrusion check (L2.code.extrusion). The
  walkers rebuild terms with `code/make` instead, which takes names as given;
  an inlining bug with colliding names came from exactly this.
- **It knows only its rules.** Each optimization is a separate pass with
  its own idea of what is known. Combining them (a branch decided by an
  inlined callee applied to a data definition) needs the passes in the
  right order, repeated.
- **It is not the semantics.** The rules are a second description of what
  Core means, next to the machine and the formal semantics.

Staging solves all three (Amin and Rompf, *Collapsing Towers of
Interpreters*, POPL 2018; Rompf's LMS; Jones, Gomard and Sestoft's partial
evaluation). The generator *is* an interpreter: run on known values it
computes, run on unknown ones it emits code, and the boundary moves with
what is known. Every binder it creates comes from a code template, so
hygiene and the extrusion check hold by construction.

## The shape

```text
 reference Code ──view──▶ term structure (read only: views for every construct)
                              │
                              ▼  gen : term × env × facts → BT
                      ┌───────────────────┐
  env: name → BT      │ static  v         │  a known value: compute with it
  facts: profiles,    │ dynamic code      │  unknown: emit code
  data definitions,   └───────────────────┘
  purity, budget          │
                          ▼
                residual Code (built only with code / esc / lift)
                          │
                          ▼  kernel: check ≡ reference, lower, install (unchanged)
```

A binding-time value (BT) is `(static v)` or `(dynamic c)`. `reify` turns
a BT into Code: a static value is lifted, a dynamic one is its code.

```clojure
(defn gen [c env]
  (let [v (code/view c)]
    (case (:op v)
      :const (static (:value v))
      :local (get env (:name v))
      :if    (let [t (gen (:test v) env)]
               (if (static? t)
                 (gen (if (value t) (:then v) (:else v)) env)        ; decided now
                 (dynamic (code (if (esc (reify t))
                                  (esc (reify (gen (:then v) env)))
                                  (esc (reify (gen (:else v) env))))))))
      :let   (let [i (gen (:init v) env)]
               (if (static? i)
                 (gen (:body v) (assoc env (:name v) i))
                 (dynamic (code (let [x (esc (reify i))]              ; a fresh binder
                                  (esc (reify (gen (:body v) (assoc env (:name v) (dynamic (code x)))))))))))
      :app   (gen-app v env)
      ...)))
```

The generator is written once, against a small *domain* interface (lift a
constant, build an `if`, a `let`, a call, a function); instantiated with
values it is an interpreter (used to test it against the machine),
instantiated with Code it is the specializer. This is the tagless-final
form of stage polymorphism.

## Where facts enter

Each kind of knowledge is one place in `gen`, not a pass:

| Knowledge | Source | What `gen` does |
|---|---|---|
| constants, data definitions | the term, the world (L4.check.delta-data) | static values |
| pure host functions on static arguments | the checker's table (L4.check.prim) | computed now |
| a known function (definition, literal) applied to static arguments | the term, the world | unfolded, within the budget |
| a branch the profile never saw taken | `if` profile | `(if guard <generated hot branch> <generated reference>)` |
| an argument that was always the same value | entry profile | `(if (same? x c) <generated with x static> <generated with x dynamic>)` |
| a call site that always called the same function | call profile | inlined under `(identical? f known)` |
| purity, totality | facts (L4.facts.*) | which calls may be computed, moved or dropped |
| budget | the preparation job | how far to unfold; past it, emit the call |

**Speculation without splicing.** The else branch of a speculation is the
reference's meaning at that point. Instead of splicing the reference's
open subterm, `gen` generates it again with everything dynamic. The result
is the reference subterm up to renaming, which the checker relates by
L4.check.alpha, and every binder in it is fresh.

**Loops** stay loops: a loop whose variables are dynamic is emitted as a
loop (its body generated once, its parameters dynamic). A loop whose bound
is static and small may be unrolled within the budget.

**Constructs the generator does not specialize** (`try`, interop,
`letrec`, `def`, code templates, functions with several arities) are kept
whole: their free locals are replaced by the code of their values. The
generator binds every non-trivial dynamic value with a `let` first, so that
code is always a local, a constant or a global, and the substitution
neither repeats work nor moves it. A substituted template keeps its
cross-stage uses (`:free`) in step with its body, which `t/substitute` now
maintains. The checker relates these constructs part by part
(L4.check.alpha) and templates as syntax up to their own binders
(L4.check.code).

What one profile fact looks like in a residual, for the expression
interpreter `calc` called 200 times on the same model
`[:+ [:* :x :x] 3]`:

```clojure
(fn self [p0 p1]
  (if (klara.jit/same? p0 [:+ [:* :x :x] 3])
    (+ (* (get p1 :x) (get p1 :x)) 3)          ; the model's arithmetic, no interpreter
    (if (number? p0) p0 ...)))                 ; the fallback: calc, generated again
```

## What stays the same

- The kernel: candidates are checked against the reference as before. The
  generator is untrusted; its residuals are checked like any other.
- The specializer interface: `(fn [ctx default] code)`. The staged
  interpreter becomes `jit/default`; user specializers still wrap it or
  replace it, and may call `gen` with their own facts.
- Views stay, for reading. Construction goes through templates.

## Later: correct by construction

Because the generator implements Core's semantics, its correctness is one
theorem about the formal semantics: for every term, environment of
binding-time values and facts, the residual means what the term means
(partial evaluation correctness). With it, residuals need no check beyond
their speculation guards; until then, every residual is checked.

## Plan

See [PLAN.md](PLAN.md), phase P7.
