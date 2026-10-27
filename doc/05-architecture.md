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
