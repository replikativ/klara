# Klara architecture

This document describes how Klara is built: the pipeline from source to
machine code, the contract a host must satisfy, the execution tiers, the
compiler as a Klara program, and the commuting squares that state what
"correct" means for each part. It merges the former `architecture.md` and
`architecture-synthesis.md` (their process history is in
`background/`).

Most of this document is design. Each section says what exists. In short:
S1 (`src/klara/{core,world,expand,eval,defs,stage}.clj`) implements the
expander, worlds, the T0 interpreter and the specialization cache; S3
(`src/klara/fusion*.clj`) implements one certified T3 rewrite; `spec/`
holds the small-step semantics in ansatz. S8 adds named K1, guarded scalar
passes and a Clojure-form emitter for a conservative subset. K2 unboxed
layouts, a dedicated K3 backend and a second host remain design. See
`background/impl/S1.md`, `S3.md` and `S8.md`.

Three views of one system:

- the **pipeline** view: what runs, and who owns each stage (§1–§6);
- the **algebraic** view: what the objects and maps are (§7);
- the **semantic** view: which squares must commute (§8, and
  `semantics.md` for the rules).

## 1. The pipeline view

Klara is not JVM-only. The design separates a small **host contract** (the
Klara Runtime Interface, KRI) from everything else, which is Klara code and
therefore portable: the expander, the analyzer, the specializer, the
optimizer policies and the standard library. Porting Klara to a new host
means implementing the KRI and one emitter; the optimizing pipeline comes
along.

```
                    ┌──────────── planning (meta level, budgeted) ───────────┐
                    │  predictor ladder: 0a types (cheap, always on)          │
                    │  0b refinement/proof (VOC-scheduled) · 1 cost models    │
                    │  2 learned surrogates · 3 profiles · 4 real runs        │
                    └──────┬───────────────────────────────▲─────────────────┘
                           │ decisions (what to specialize)│ receipts, evidence
                           ▼                               │
 source ──expand──▶ Core K0 ──analyze──▶ K1 effect-lowered ──specialize──▶ K2 ──emit──▶ K3
   (world reads      (12 forms,          (op classes:        (guards,          (JVM bytecode
    recorded)         CodeIds)            tail/abort/general) shapes, layouts,  │ Chez Scheme
                                                              certificates)     │ C/LLVM via
                                                                                │ metacarp
                                                                                ▼
                     ┌──────────── host: KRI ─────────────────────────────────────┐
                     │ values · memory · control · world cells · code load/guard  │
                     │ fibers · FFI · counters                                    │
                     └────────────────────────────────────────────────────────────┘
```

The IR ladder in more detail:

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

**Ownership rule.** Klara owns everything that reads the world: expansion,
analysis, specialization, guards, invalidation and the predictor ladder. A
host back end (JVM emitter, Chez, metacarp) only turns closed K3 code into
machine code. Chez is the planned native baseline; metacarp/LLVM is the
kernel route (T3).

| Stage | Status |
|---|---|
| expand (scope sets, recorded reads incl. negative lookups, CodeIds) | implemented, `klara.expand` (S1) |
| K0 = Klara Core, 12 forms as maps | implemented, `klara.core` (S1); formal version in `spec/` |
| T0 interpreter of K0 | implemented, `klara.eval` (S1) |
| specialization cache, guards, certificate-checked install | implemented, `klara.stage` (S1) |
| one T3 rewrite (map/filter/reduce fusion, ansatz certificate) | implemented, `klara.fusion` (S3) |
| named K1, guarded inlining, partial evaluation, scalar replacement, Clojure emission | implemented for a conservative subset, `klara.compile` (S8); tested, not proved |
| full K2 layouts, dedicated K3 emitters, predictor ladder | design |

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

A host that implements the KRI and an **interpreter for K0** runs all of
Klara immediately, slowly. Adding a K3 emitter makes it fast. The
specialization decisions (what to specialize, which guards, which rewrites)
are portable Klara code and do not change per host.

Today the only host is the JVM, through Clojure 1.12: S1 uses Clojure's
persistent collections (phase 0), one atom per world with a CAS loop for
publication, and host IFns for executables. The world is a single
reference to an immutable root, so publication is one CAS and a reader
never sees a half-published state.

## 3. Execution tiers

| Tier | What | Written in |
|---|---|---|
| T0 | interpreter of K0 | Klara (portable) or a host seed (sci on JVM/JS, a small C interpreter natively) |
| T1 | S8: Clojure-form emission for a conservative subset; full generic-call coverage remains design | Clojure seed compiler + public Clojure `eval` |
| T2 | S8 front half: guarded inlining, local scalar replacement, lexical tail/abort lowering; shapes and unboxed layouts remain design | Clojure seed passes + host emitter |
| T3 | certified kernels: law- or proof-licensed rewrites (wandler/raster style) | Klara + ansatz certificates |
| collapse | AOT artifact under a closed-world manifest | the same pipeline with all cells declared static |

Tiers are caches, never dependencies: deleting T1–T3 changes no
observation (gate R3, tested in `stage_test` and `fusion_test`). On
C/LLVM, compile latency is higher than on the JVM, which makes T0 and
staging more important there, not less.

Per host:

| | JVM | native (Chez) |
|---|---|---|
| T0 | sci-style interpreter (today: `klara.eval`, a CEK machine in Clojure) | Petite-style interpreter for huge/trivial forms |
| T1 | S8: Clojure-compiled subset | Chez-compiled generic code, var indirection, no inlining across cells |
| T2 | S8: guarded scalar passes; HotSpot optimization | Chez-compiled specialized code with guards (Klara supplies speculation; Chez has none) |
| T3 | raster kernels (today: S3's fused host functions) | metacarp/carpaccio kernels |
| continuations | selective CPS (measured 2.7× tax on transformed code) | segmented stacks (no tax on non-capturing code; needs no mutable-local lowering and an authority scan before a second resume) |

**Effects on the JVM** (from the handler probe, `experiments/handlers/`,
OpenJDK 25 C2; read the ratios): a tail-resumptive operation through a
handler costs 1.18× a protocol call while a site sees at most two clause
types (7.7× at three); an unused handler frame is nearly free (installing
one ≈11 ns); CPS-compiled code is 2.7× slower even when no perform fires;
Loom continuations cost 250 ns per perform and are one-shot only
(rejected). Hence operations are classified tail / abort / general at
definition time, and CPS regions must be narrow (RFC 0002).

## 4. The compiler is made of values

- Every IR is a value; every pass is a staged function from IR to IR; pass
  results are tracked nodes keyed by (input CodeId, assumptions), so the
  compiler is incremental and forkable like any other Klara computation.
- Rewrite rules are world values with law certificates; the optimizer is a
  policy over them, also a value.
- Each pass carries a correctness obligation (a simulation between source
  and target semantics). Passes are certified (ansatz), differentially
  tested, or trusted, and the receipt of an executable says which.

What exists: the expander already runs this way. Macros are world values,
expansion records its reads, and re-expansion after an edit is incremental
with early cutoff on the CodeId (`klara.defs/invalidate!`). The fusion
certificate (S3) records its checker, laws, cohort and dependency closure.

### 4.1 Interpreter plus specializer gives a compiler

With `specialize` in the core (s-m-n), the first Futamura projection says
specializing the T0 interpreter to a program yields compiled code for it.
PyPy (RPython meta-tracing) and Truffle/Graal (partial evaluation of AST
interpreters) obtain JITs from interpreters this way. For Klara it would
mean writing the T0 interpreter in Klara once and obtaining T1/T2 by
specializing it per host. Both precedents took years and need careful
binding-time engineering of the interpreter. The realistic path is a
direct compiler for T1/T2 first, with the Futamura route as a research
track.

### 4.2 The compiler under its own staging lens

The compiler's inputs have different binding times:

| Input | Changes | Grade |
|---|---|---|
| compiler code, pass definitions, rule sets, policies | rarely (compiler development) | stable, versioned in the world |
| host description (KRI, emitter, CPU features) | per deployment | static per build |
| the program being compiled | per definition version | static per CodeId |
| profiles and assumptions | revocable | assumption sets (guards) |
| runtime data | always | dynamic |

Consequences:

1. **The compiler specializes itself** on the stable inputs: passes and
   rule matchers compiled for the current rule set and host. Changing a
   rule invalidates only the matcher specializations that read it.
2. **Compiler development has the application workflow.** Passes are
   world definitions with recorded reads, so editing a pass invalidates
   only cached results that used it; a new pass can be tried in a fork,
   compared differentially against the old compiler's outputs, and adopted
   with a receipt.
3. **Correctness transfers.** If a pass is proved correct, its
   specializations are correct by the s-m-n law (specialize-then-run ≡
   run); no proof per specialization is needed.
4. **Towers collapse.** User-level DSLs (wandler pipelines, foerster
   models) are interpreters on top of Klara; specializing through the
   tower removes the interpretive layers (Amin–Rompf).
5. **The Futamura projections are concrete**: specializer + interpreter =
   compiler (1st/2nd); specializer applied to itself = compiler generator
   (3rd). Self-hosting is the collapse whose output must hash to the
   shipped artifact.
6. **Compile time is a budgeted resource**: compile iff expected saved
   cost exceeds compile cost; the compiler's own costs appear in receipts.

Hazards: the specializer must terminate when applied to itself (fuel,
generalization); code size; debuggability; bootstrap order (a seed compiler
must exist before it can specialize itself). Early stages must not depend
on self-specialization for acceptable compile speed.

**Chez Scheme's counterpoint.** Chez compiles every REPL form to machine
code through a nanopass pipeline (Keep & Dybvig) fast enough that it needs
no interpreter tier and no JIT. For native hosts this suggests replacing
T0/T1 with a Chez-style fast compiler (many small passes, careful IR
representations) and keeping speculation and guards only for T2. The pass
framework could build on `pattern` (rule-based rewriting over persistent
data, nanopass-style dialects), once it generates matcher code (it is
25–33× slower than hand-written passes today).

## 5. One definition traced through the layers

```clojure
(defn f [xs] (reduce + (map inc xs)))
```

1. **expand** → core term; CodeId `h1`; recorded reads: `reduce`, `map`,
   `inc`, `+` (bindings and their versions). *Implemented.* (In S1,
   clojure.core names that the world does not define are recorded as
   negative lookups and become ambient `:host/call` performs.)
2. **T1**: generic executable for `h1`, calls through var indirection.
   *Design; today T0 interprets the term.*
3. **profile**: `f` is hot; `xs` is always a vector of longs. *Design.*
4. **specialize** `h1` with guard `xs : (vector long)`; the fusion rule
   (map/reduce → single fold, licensed by the Foldable law plus purity of
   `inc`) fires; its certificate comes from ansatz. *Implemented for this
   shape in S3, gated by an explicit shape claim instead of a profile, and
   with the guard `[:arg 0 :nat-list]`.*
5. **effect lowering**: no effects in the region → plain direct code.
   *S3 checks that the stages perform nothing and guards against a dynamic
   handler of `:host/call`.*
6. **emit** K3 and **install** with (CodeId `h1`, guards, certificate).
   *S3 emits a Clojure function and installs it through `klara.stage`,
   whose `:ansatz/kernel` checker rechecks the proof.*
7. **edit** `inc` at the REPL → `h1`'s recorded read of `inc` is dirty →
   the executable's guard fails; calls fall back to the generic path at
   once; the specializer re-runs (in S3, explicitly via `optimize!`).

## 6. The predictor ladder: the specializer is planned on a meta level

The specializer is itself budgeted and steered by cheaper, coarser
predictors, as in AutoML or Bayesian optimization: predictions that are
faster than running the underlying system decide where the expensive
computation goes.

| Level | Predictor | Cost | Licence of its predictions |
|---|---|---|---|
| 0a | cheap static analysis, always on: shapes with occurrence typing, op classes and latent effect rows, captures with affine authority | ~free at compile time | *certified*: sound over-approximation |
| 0b | refinement types / SMT, ansatz proofs | expensive; scheduled by value of computation | *certified* |
| 1 | analytic cost models (op counts, cardinality estimates, roofline) | µs | estimate with a stated error model |
| 2 | learned surrogates (cost models trained on receipts, GP/BO over schedules) | µs–ms | *statistical*: calibrated on held-out receipts |
| 3 | profiling and sampled measurement | ms–s | measurement with provenance |
| 4 | the actual run | full | ground truth |

Principles:

1. **Each predictor is a translation to a coarser model** with an error ε.
   Planning the compiler is inference over a tower of models of the
   program's own behaviour. Type systems are the exact, cheap end of this
   tower.
2. **Value of computation decides**: refine a prediction only when the
   expected improvement in the decision is worth the cost; specialize only
   when predicted savings × expected executions exceed compile plus
   verification cost.
3. **No infinite regress**: each meta level gets a budget that is a bounded
   fraction of the expected savings of the level below; the top level is a
   fixed, simple heuristic.
4. **Predictors learn from receipts**, with the evidence discipline:
   the evidence used to select a plan is kept apart from the evidence used
   to claim its gain.
5. **Predictions never replace certificates**: a level 1–3 prediction may
   steer which rewrite to try; only a level-0 fact or a guarded check
   licenses running it.

Further rules (research note J): sound facts that read other definitions
need no runtime guard but are invalidated on publication; facts about
Tier H host code are always guarded or recorded as trusted. The prediction
that pays most is op-class absence plus latent effects (Koka decides CPS
this way): it decides where CPS regions and guards go. ansatz laws over
`Nat` need an overflow side condition before they license rewrites on JVM
longs (S3 implements one: exact-or-throw lowering plus deopt).

Status: design. S3's shape claim is a hand-written level-0 fact, checked at
entry; no predictor runs automatically.

## 7. The algebraic view: objects and maps

```
          Data  ─────────── acts on ───────────▶  Authority world
   (monoidal computer:                         (linear: tokens for consume,
    values, programs P,                          branch, settle, evidence,
    copy/discard on all,                         budget, randomness;
    run : P⊗A→B,                                 split rules per kind;
    specialize : P⊗A→P)                          no copy)
```

- **Terms and programs**: Core terms modulo α; programs P are closed code
  values with CodeIds.
- **Handlers** are algebras for effect signatures; a reference handler
  fixes each effect's meaning; λ∨'s laws are equations the reference
  handlers satisfy; inference engines are other models.
- **Algebras as values** (stdlib): monoid, join (commutative monoid
  classified by divisibility), distance, measure, deltas, passed
  explicitly; their laws license rewrites at a stated level (proved /
  tested / documented).
- **Translations** T : model₁ → model₂ (compile, marshal, offload,
  coarse-grain) are **lax**: they preserve meaning up to an error ε and are
  *not* functorial in cost (fusion is the counterexample).
- **Predictors** are **abstract interpretations**: a Galois connection
  α : concrete ⇄ abstract : γ per analysis (shapes, effects/op classes,
  captures/authority, refinements, grades); several combine as a reduced
  product over one AST.
- **Specialization** is s-m-n on P: `run(specialize(p,a), b) = run(p,(a,b))`.

## 8. The semantic view: squares that must commute

Each correctness claim in Klara is one commuting square, exact or up to ε.
The status column refers to `semantics.md` §8, which has the details.

**Adequacy (A1).** Operational and denotational semantics agree on
observations. *Stated, not proved; no denotational model for Klara Core
yet.*
```
   e ──── ⟶* (small-step, reference handlers) ────▶ observations
   │                                                     ▲
   ⟦·⟧                                                   │ obs
   ▼                                                     │
 weighted execution tree ────────── limit/normalize ─────┘
```

**Pass correctness.** Every compiler pass Kᵢ → Kᵢ₊₁ is a simulation.
*No IR passes exist yet; S3's fusion is certified per pipeline, its
elaborator and lowering are trusted and tested.*
```
   Kᵢ term ──── pass ────▶ Kᵢ₊₁ term
     │                        │
   ⟦·⟧ᵢ                     ⟦·⟧ᵢ₊₁
     ▼                        ▼
   meaning ─────── = ──────▶ meaning        (certified, tested, or trusted —
                                              recorded in the receipt)
```

**Specialization (s-m-n, A2(ii)).** Residuals are correct by construction
once the specializer is; proved passes stay proved when specialized.
*Proved in `spec/` for the trivial specializer at values; tested in T0.*
```
   (p, a, b) ── specialize(p,a), then run on b ──▶ result
       │                                              ║
       └──────────── run p on (a,b) ─────────────────▶ result
```

**Guarded specialization.** Under the assumption set A (world cells,
argument guards), the residual agrees with the generic program; when A
fails, control returns to the generic path at region entry (replay)
without repeating effects. *Tested (R3) in S1 and S3.*
```
   x ── guard_A(x)? ──yes──▶ residual(x) ─┐
        │                                  ├──▶ same observation
        └──no──▶ generic(x) ───────────────┘
```

**Predictor soundness.** An abstract fact over-approximates every concrete
run (γ ∘ α ⊒ id); a fact licenses a rewrite only if its level is 0a/0b.
*Design.*

**Translation (approximate).** `d(⟦T e⟧, ⟦e⟧) ≤ ε(T)` under the declared
metric; ε composes along pipelines by the error algebra (Lipschitz
composition); cost is measured. *Design.*

**Snapshot fork.** Forking commutes with the world: a branch observes the
pinned parent root; authorities split exactly once (RFC 0001). *Snapshot
part tested in S1; authority split not implemented.*

### Where the formal semantics sit

| Layer | Semantics | Status |
|---|---|---|
| Klara Core | small-step operational (needed for effects, divergence, stuck states) | **written and kernel-checked** in ansatz, `spec/` (S2): 12 forms, lexical deep handlers, determinism, preservation, progress, s-m-n |
| Klara Core | big-step semantics for terminating fragments | not yet written |
| Klara Core | denotational: weighted execution trees with limits (Staton et al.) | stated in `background/01-core-v2.md` §5; λ∨ has a measure semantics for its first-order fragment |
| Core ↔ model | adequacy A1/A2/A3 | stated (research note A); A3 open |
| each IR pass | simulation between adjacent IRs | per pass: certified, tested or trusted |
| λ∨ fragment | mechanized (Lean): first-order, footprint-typed, weights elided | in the lambda-join repository |

Recommended order: the small-step semantics (done), a big-step semantics
for the terminating, effect-free fragment proved equivalent to it, then the
denotational model and adequacy for the discrete fragment.

## 9. Decisions

Accepted (Christian, 2026-10-27), from research notes I and J:

1. Chez as a native **host** first (hybrid), not only a blueprint.
2. Native memory: Chez's tracing GC gives up reference-counting reuse;
   acceptable for the first native tier, revisited after the memory
   experiment.
3. Operation classes (tail / abort / general) stay **semantic** on every
   host, even where segmented stacks would make them a hint.
4. `pattern` needs matcher code generation before it carries hot passes;
   that work goes upstream.
5. Held-out evidence discipline is covered by no type system; it stays a
   runtime evidence rule.
6. The Typed Clojure fork's own files (solely Christian's) may be
   relicensed and ported; upstream Typed Clojure files remain EPL and are
   used for ideas only.

Implementation steps and where they stand:

| Step | Content | Status |
|---|---|---|
| S1 | core syntax, worlds with one publication protocol, basis-specific execution, the expander producing core terms, T0 with reference handlers, the specialization cache with certificate-checked install | done (`background/impl/S1.md`) |
| S2 | small-step semantics for the 12 forms in ansatz | done (`spec/README.md`); differential run against T0 pending |
| S3 | map/filter/reduce fusion as a law-licensed rewrite with an ansatz certificate | done (`background/impl/S3.md`) |
| staging | code values, `code`/`esc`/`run`/`lift`, let-insertion, the REPL and transcript harness | implemented (`guide/05-staging.md`); not yet in the formal spec |
| next | authority accounting (RFC 0001), op classes, a T1 emitter | design |

## JIT primitives the staging mechanism must provide (from research notes K and M, 2026-10-28)

Notes K (GraalVM/Truffle) and M (V8) arrive independently at the same list:

1. **Per-root validity caching.** Worlds are immutable, so an executable's
   validity depends only on the basis root: check once per root, cache the
   verdict. Avoids both per-entry re-checking of every global (S1 today) and
   V8-style killing of dependent code (which breaks gate R1).
2. **Frame states and `deopt`.** Entry-only guards can speculate on arguments,
   captures and handlers but not on intermediate values, where most speed
   comes from. Generated code carries frame states and rebuilds a T0 machine
   state on a cold path (T0 continuations are data, so no special emitter is
   needed). The same mechanism serves deopt, capturing a continuation for a
   general effect, forking, and inspection.
3. **Site identity and feedback.** Content-addressed CodeIds merge identical
   code at different call sites, so feedback is keyed by (CodeId, site);
   monotone, capped. Feedback is a separate predictor rung (3a): always on,
   nanoseconds.
4. **Assumptions in code values**, re-checked at install; pinned bases make
   V8-style lazy deopt (stack patching) unnecessary as long as assumptions
   range only over world cells, shape versions and immutable data.
5. **`run` that compiles and installs**, with pure specialization jobs
   installed by compare-and-set (concurrent, never on the critical path).
6. **OSR** via self tail calls through the entry hook, taking the
   interpreter's loop bindings.
7. **Aging/eviction** and at most ~4 cache entries per function.
8. **Post-PE optimization matters most** (K, PLDI 2017 measurements): escape
   analysis gives an order of magnitude, assumption folding 2–3×; partial
   evaluation alone removes little. Klara's `specialize` must feed a real
   optimizer, not stop at partial application.

On the JVM, HotSpot is the optimizing tier; Klara's T2 fills the
Maglev-like mid-tier slot. No separate mid tier.

## Web targets (research note L)

JS first: collapsed ES modules (closed-world, every baked assumption
recorded, results identical to T0) and a dynamic mode in which the JVM
compiles each definition to a module the page loads by URL (works under a
strict CSP; the compiler is never shipped). WasmGC for numeric kernels only.
Avoid ClojureScript's top-level registration pattern, the main source of its
payload. Multi-shot effects need CPS or replay on every web target (JSPI and
Wasm stack switching are one-shot). Size precedents: squint 2.0 KB gzip hello
world, cljs advanced ~23 KB, immutable.js Map alone 18.6 KB.

## Data format: EDN (decision, 2026-10-28)

Klara commits to **EDN** for all of its data: receipts, certificates,
manifests, world and code serialization, RFC artifacts, effect payloads.
Identity, versioning and provenance are expressed with namespaced keywords
and tagged literals (`#inst`, `#uuid`, plus Klara tags). Two consequences:

- **Canonical encoding for hashing.** Content addressing (CodeIds, receipts,
  certificates) needs one canonical byte encoding of EDN values: sorted map
  keys and set elements by a total order, normalized numbers, no metadata in
  the hash. This must be specified once and used everywhere.
- **Other formats only at boundaries**, and only where they add something EDN
  lacks: JSON-LD (globally resolvable IRIs, W3C PROV vocabularies) for
  exporting provenance to external systems; JSON for web interop. They are
  projections of the EDN data, never the source of truth.

## Languages as world values: the language lattice (draft, 2026-10-28)

Christian's framing, to be refined with research note O (Racket):

- **Languages are first-class world values**, versioned and forkable like
  code; their histories are exposed through geschichte's git interface.
- **EDN with persistent-memory semantics is the centre.** Languages are
  built around it and may support only a subset of it. A language L has a
  value domain V_L; between two languages, values in the shared subset
  V_L ∩ V_M cross **without checks or conversion**, so lifting (in the
  multi-stage sense of Amin and Rompf) is the identity. A boundary check is a
  membership test for the shared subset — the same object as a staging guard:
  when types or other predictors establish membership statically, the check
  is erased.
- **Three boundary cases** between an inner language L and the host M:
  1. *L is a sublanguage of M* (same semantics, fewer capabilities): run L's
     programs on M itself, in a forked world under a restricted handler stack
     and authority set. No interpretive layer; isolation comes from forks and
     authorities, not from nesting interpreters. This is what dvergr and
     spindel already do for nested sci rooms: they do not interpret the sci
     interpreter, they run the top-level interpreter in an isolated fork.
  2. *L shares values with M but has different semantics* (another evaluation
     order, numeric model, a Datalog engine): `interpret_L` written in Klara,
     specialized per fragment by staging (first Futamura projection);
     boundary checks only for values outside the shared subset.
  3. *L has foreign values* (host objects, language-specific
     representations): an explicit translation with conversion cost; staging
     can still fuse conversions away.
- Case 1 requires that "the same language" includes the same effects and
  world semantics, and that isolation also covers host interop
  (irreversible effects deferred per RFC 0001); otherwise a nested
  environment could escape through the host.
