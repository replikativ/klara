# Klara architecture: runtime and compiler abstractions (draft, 2026-10-27)

Klara is not JVM-only. The design separates a small **host contract** (what
each substrate must provide) from everything else, which is Klara code and
therefore portable — including the expander, the specializer, the optimizer
policies and the standard library. Writing the JIT "inside out", in the
language, is what makes a new host cheap: port the contract and one emitter,
and the whole optimizing pipeline comes along.

## 1. The picture

```
 surface (Clojure-compatible reader, syntax extensions)
        │ expand            ← Klara code: scope sets, recorded reads, CodeIds
        ▼
 Klara Core (12 forms)      ← the specification: operational + denotational semantics
        │ analyze           ← Klara code: AST with evidence slots, content hashes
        ▼
 IR ladder (nanopass; every pass a tracked, cached function over IR values)
   K0  core IR (untyped, effects as perform/handle)
   K1  effect-lowered IR    tail ops → direct calls; abort → stackless exceptions
                            / longjmp; general → narrow CPS regions or heap frames
   K2  specialized IR       guards, assumptions, shapes, unboxed layouts,
                            uniqueness evidence (typed, evidence-carrying)
   K3  backend IR           JVM bytecode │ C │ LLVM IR │ Wasm │ JS
        │ emit + load       ← per host
        ▼
 Klara Runtime Interface (KRI)  ← per host: the only non-portable layer
```

Everything above the KRI is the same program on every host. The emitter for
K3 is per host but small (raster's JVM emitter, metacarp/carpaccio's C
backend, metacarp's LLVM backend exist).

## 2. The host contract (KRI)

What a substrate must provide, and how the existing hosts would provide it:

| Concern | Contract | JVM | Native (C/LLVM) | Wasm / JS |
|---|---|---|---|---|
| Values | immediates, boxed objects, `=`/hash per spec | objects, Clojure interfaces | tagged pointers, RC headers | WasmGC structs / JS objects |
| Persistent collections | CHAMP/RRB per the portable spec | Klara classes (or Clojure's in phase 0) | C structs with RC | per host |
| Memory | allocate, reclaim, uniqueness evidence, freeze | tracing GC; region tokens | RC with reuse (Perceus-style); arenas | GC (WasmGC/JS) or linear RC |
| Control | call, self tail call, abort, resumable frames | exceptions; CPS on heap | longjmp/unwind; segmented stacks or CPS | exceptions; CPS |
| World | cells, pinned basis, atomic publication (release/acquire) | VarHandles, CAS | atomics | atomics / single thread |
| Code | load an executable, guard, invalidate, install with certificate | hidden classes, SwitchPoint/MutableCallSite | dlopen / LLVM ORC JIT; version words | `WebAssembly.instantiate` / `Function` |
| Concurrency | fibers/tasks, scheduler | virtual threads / executors | threads + work stealing | workers / event loop |
| Interop | foreign calls, host objects as resources | Java interop, Clojure IFn | C ABI (Panama on JVM side) | JS interop |
| Observation | counters, sampling for profiles | JFR / counters | perf counters | performance API |

A host that implements the KRI and an **interpreter for K0** runs all of Klara
immediately (slowly). Adding a K3 emitter makes it fast. The specialization
decisions — what to specialize, which guards, which rewrites — are portable
Klara code and do not change per host.

## 3. Execution tiers

| Tier | What | Written in |
|---|---|---|
| T0 | interpreter of K0 | Klara (portable) or a host seed (sci on JVM/JS, a small C interpreter natively) |
| T1 | baseline compile: generic code, var indirection, no assumptions | Klara compiler + host emitter |
| T2 | specialized: guards, effect erasure, shapes, unboxed layouts | Klara specializer + host emitter |
| T3 | certified kernels: law- or proof-licensed rewrites (wandler/raster style) | Klara + ansatz certificates |
| collapse | AOT artifact under a closed-world manifest | the same pipeline with all cells declared static |

Tiers are caches, never dependencies: deleting T1–T3 changes no observation
(gate R3). On C/LLVM, compile latency is higher than on the JVM, which makes
T0 and staging more important there, not less.

## 4. The compiler is made of values

- Every IR is a value; every pass is a staged function from IR to IR; pass
  results are tracked nodes keyed by (input CodeId, assumptions), so the
  compiler is incremental and forkable like any other Klara computation.
- Rewrite rules are world values with law certificates; the optimizer is a
  policy over them, also a value.
- Each pass carries a correctness obligation (a simulation between source and
  target semantics). Passes are certified (ansatz), differentially tested, or
  trusted — and the receipt of an executable says which.

## 5. The elegant route: interpreter + specializer = compiler

With `specialize` in the core (s-m-n), the first Futamura projection says
specializing the T0 interpreter to a program yields compiled code for it. This
is how PyPy (RPython meta-tracing) and Truffle/Graal (partial evaluation of
AST interpreters) obtain JITs from interpreters. For Klara it would mean: write
the T0 interpreter in Klara once; obtain T1/T2 by specializing it per host.
Risk: both precedents took years and need careful binding-time engineering of
the interpreter. Realistic path: a direct compiler for T1/T2 first, the
Futamura route as a research track (the monoidal-computer reading of D1 makes
it a natural experiment).

## 6. One definition traced through the layers

```clojure
(defn f [xs] (reduce + (map inc xs)))
```

1. **expand** → core term; CodeId `h1`; recorded reads: `reduce`, `map`,
   `inc`, `+` (bindings and their versions).
2. **T1**: generic executable for `h1`, calls through var indirection.
3. **profile**: `f` is hot; `xs` is always a vector of longs.
4. **specialize** `h1` with guard `xs : (vector long)`; the fusion rule
   (map/reduce → single fold, licensed by the Foldable law plus purity of
   `inc`) fires; its certificate comes from ansatz (or the law is
   property-tested and the rewrite stays guarded).
5. **effect lowering**: no effects in the region → plain direct code.
6. **emit** K3 (bytecode on the JVM, C or LLVM natively); **install** with
   (CodeId `h1`, guard, certificate).
7. **edit** `inc` at the REPL → `h1`'s recorded read of `inc` is dirty → the
   T2 executable is invalidated; calls fall back to T1 immediately; the
   specializer re-runs in the background within its budget.

## 7. Where the formal semantics sit

| Layer | Semantics | Status |
|---|---|---|
| Klara Core | small-step operational (the specification; needed for effects, divergence, concurrency, stuck states) | not yet written for Klara; λ∨'s small-step semantics exists in Redex (`lambda-join/redex/lambda-join.rkt`) |
| Klara Core | big-step (natural) semantics for terminating fragments; basis of the reference interpreter and simpler proofs | not yet written |
| Klara Core | denotational: weighted execution trees with limits (Staton et al.) | stated in v2 §5; λ∨ has a measure semantics for its first-order fragment F1 (`lambda-join/redex/measure.rkt`, ESOP calculus paper App. C) |
| Core ↔ model | adequacy A1/A2/A3 | stated (research note A); A3 open |
| each IR pass | simulation between adjacent IRs | per pass: certified, tested or trusted |
| λ∨ fragment | mechanized (Lean): first-order, footprint-typed, weights elided | `lambda-join/lean/LambdaJoin/Core.lean` |

Recommended order: small-step for the 12 forms with reference handlers in
ansatz (X3), a big-step semantics for the terminating, effect-free fragment
proved equivalent to it (a standard, cheap theorem that also validates the
reference interpreter), then the denotational model and adequacy for the
discrete fragment.

## 8. The compiler under its own staging lens (discussion, 2026-10-27)

The compiler's inputs have different binding times:

| Input | Changes | Grade |
|---|---|---|
| compiler code, pass definitions, rule sets, policies | rarely (compiler development) | stable, versioned in the world |
| host description (KRI, emitter, CPU features) | per deployment | static per build |
| the program being compiled | per definition version | static per CodeId |
| profiles and assumptions | revocable | assumption sets (guards) |
| runtime data | always | dynamic |

Consequences:

1. **The compiler specializes itself** on the stable inputs: passes and rule
   matchers compiled for the current rule set and host (pattern's compiled
   matchers already work this way). Changing a rule invalidates only the
   matcher specializations that read it.
2. **Compiler development has the application workflow**: passes are world
   definitions with recorded reads, so editing a pass invalidates only cached
   results that used it; a new pass can be tried in a fork, compared
   differentially against the old compiler's outputs, and adopted with a
   receipt.
3. **Correctness transfers for free**: if a pass is proved correct, its
   specializations are correct by the s-m-n law (specialize-then-run ≡ run,
   A2(ii)); no proof per specialization.
4. **Towers collapse**: user-level DSLs (wandler pipelines, foerster models)
   are interpreters on top of Klara; specializing through the tower removes
   the interpretive layers (Amin–Rompf). This is how wandler-in-Klara becomes
   fast without a bespoke code generator.
5. **The Futamura projections are concrete**: specializer + interpreter =
   compiler (1st/2nd); specializer applied to itself = compiler generator
   (3rd). Self-hosting (ring 5) is the collapse whose output must hash to the
   shipped artifact.
6. **Compile time is a budgeted resource**: compile iff expected saved cost
   exceeds compile cost; the compiler's own costs appear in receipts. The
   compiler is a bounded-rational policy inside the calculus it implements —
   the MPI talk's "layered compilation as learning".

Hazards: the specializer must terminate when applied to itself (fuel,
generalization); code-size growth; debuggability; bootstrap order (a seed
compiler must exist before it can specialize itself). Early stages must not
depend on self-specialization for acceptable compile speed.

**Chez Scheme's counterpoint.** Chez (../ChezScheme) compiles every REPL form
to machine code through a nanopass pipeline (Keep & Dybvig) fast enough that
it needs no interpreter tier and no JIT. For native hosts this suggests
replacing T0/T1 with a Chez-style fast compiler (many small, simple passes,
careful IR representations), keeping speculation and guards only for T2. The
pass framework could build on ../pattern (rule-based rewriting over persistent
data, nanopass-style dialects).

## 9. The specializer is planned on a meta level (Christian, 2026-10-27)

The specializer is itself budgeted and steered by cheaper, coarser predictors,
as in AutoML or Bayesian optimization and as raster's north star prescribes:
predictions that are faster than running the underlying system decide where
the expensive computation goes.

**A ladder of predictors**, ordered by cost and fidelity:

| Level | Predictor | Cost | Licence of its predictions |
|---|---|---|---|
| 0 | type system / static analysis (abstract interpretation) | ~free at compile time | *certified*: sound over-approximation |
| 1 | analytic cost models (op counts, cardinality estimates, roofline) | µs | estimate with a stated error model |
| 2 | learned surrogates (cost models trained on receipts, GP/BO over schedules) | µs–ms | *statistical*: calibrated on held-out receipts |
| 3 | profiling and sampled measurement | ms–s | measurement with provenance |
| 4 | the actual run (real compute, the real world) | full | ground truth |

Principles:

1. **Each predictor is a translation to a coarser model** with an error ε —
   the same `translate` move as in simulation (coarse-graining). Planning the
   compiler is therefore inference over a tower of models of the program's
   own behaviour, steered by the same allocation policy that steers
   simulations. Type systems are the exact, cheap end of this tower: a sound
   predictor for certain properties.
2. **Value of computation decides**: refine a prediction (move down the ladder)
   only when the expected improvement in the decision is worth the cost;
   specialize only when predicted savings × expected executions exceed compile
   plus verification cost.
3. **No infinite regress**: each meta level gets a budget that is a bounded
   fraction of the expected savings of the level below; the top level is a
   fixed, simple heuristic.
4. **Predictors learn from receipts**, with the evidence discipline:
   measurements are split, never copied; the evidence used to select a plan is
   kept apart from the evidence used to claim its gain; surrogates are
   calibrated on held-out receipts.
5. **Predictions never replace certificates**: a level-2 prediction may steer
   which rewrite to try; only a level-0 proof or a guarded check licenses
   running it.
