# Klara — design space (iteration 0, 2026-10-27)

Working name **Klara** (after Klára Dán von Neumann, who coded the 1948 ENIAC
Monte Carlo runs). Language of the replikativ stack; replikativ.org is the
umbrella institution; Simmis is the flagship platform, not the language.
λ∨ (this repo) is the calculus. This file frames the first design iteration;
research notes go in `research/`, the synthesis in `01-core-v1.md`.

## Principles (Christian, 2026-10-27)

1. **Value semantics**, Lisp foundations (λ surface), code as data.
2. **Fast REPL turnaround**; the running system is the development environment.
3. **Features à la carte** — no Haskell/Scala-style global buy-in.
4. **Hostable into existing systems** (polymorphism, efficient dispatch,
   zero-overhead interop) — clean functional extensions and isolated
   experiments over existing systems, not rewrites; datahike's persistent
   memory model is the boundary to external state.
5. **Physical awareness of the substrate**: memory locality; computing in
   another environment requires a translation (compile, marshal, offload,
   coarse-grain) — functorial, with an error ε and a cost.
6. **Computation integrates learning dynamics** (as JITs do); the runtime's
   self-optimization and the agents' work use the same moves.
7. **Staging is a continuum**, not a static/dynamic binary: expand,
   specialize and re-expand at any stage (beyond Racket's top level).
8. **Formally specified core** (SML/Wasm standard): operational semantics in
   ansatz, kept Lean-4-checkable; corpus as the conformance suite. Spec bugs
   are acceptable and fixed by iteration; "certain" ≠ paranoid.
9. Serve both PL research/formalization and Clojure-style pragmatics.
10. Work backwards from simulation and a resource-aware calculus of bounded
    rationality (MPI talk 2026-10; raster/design/compiler-north-star.md).

## Decided in conversation (2026-10-27)

- **Copyright separate**: own license (Apache-2.0 proposed), Clojure only as
  an unmodified dependency, clean-room runtime from papers, no Clojure
  sources given to agents writing runtime code, similarity scan vs
  ../clojure/src before release, Clojure's EPL tests stay in
  ../clojure-conformance, no Clojure name/logo in branding.
- **Clojure as a library first**: use Clojure's data structures initially;
  zero-overhead both ways (Klara values implement clojure.lang interfaces,
  hasheq parity; Clojure IFns dispatch natively). Two loading modes:
  *linked* (plain require; state outside forks, Tier H) and *hosted*
  (through Klara's expander; defs in the world, forkable).
- **Dynamic core + narrowing layers** (shapes → affine → grades → proofs),
  each satisfying a gradual-guarantee-style obligation: annotations reject
  programs or license representations, never change meaning.
- **MC substrate, λ surface** (already D1): programs are values (P), `run`,
  `specialize`; adequacy theorem links λ operational semantics to the MC model.
- **Forkable = copyable**: values carry a copy comonoid, resources don't;
  affine inside regions, persistent across fork boundaries, `freeze` at the
  boundary; uniqueness by RC=1 (owned runtime, Perceus) or static proof
  (affine types / escape analysis on JVM). (Already in doc/signature.md §1 —
  the CD-category table.)
- **Binding time as a grade** (static ⊑ stable ⊑ dynamic, D2), expansion as a
  tracked, cached, invalidatable effect; `eval` ships first.
- **Meaning fixed by spec; operational choices learned; certificates bridge.**
  JIT decisions carry receipts and replay.
- Community: neutral Klara space (Zulip proposed), RFC repo canonical,
  #klara on Clojurians as bridge.

## Prior design to build on (read before proposing)

doc/language.md (v2), doc/design-decisions.md (D1–D20), doc/algebras.md,
doc/state.md, doc/signature.md, doc/narrowing.md, doc/bootstrap.md
(growth rings), doc/lambda-v.md, studies/*.md (23 language studies: koka,
lean4-runtime, graal-truffle, julia, roc, valhalla, racket-rhombus, unison,
…), v0/src/v0/* (rings 0–4 implementation), redex/, lean/.
Sibling repos: ../raster (typed dispatch, escape analysis, bytecode emitter,
design/compiler-north-star.md), ../carpaccio + ../metacarp (affine/borrow
checked native), ../wandler (certified rewriting runtime over ../ansatz),
../ansatz (Lean 4 kernel in Clojure), ../spindel and ../partial-cps
(forkable reactive execution, continuations), ../datahike ../konserve
../yggdrasil (persistent memory, branches, merge), ../gatlab-clj (katzen:
AlgebraicJulia port, programs as string diagrams), ../foerster (inference
over forkable worlds), ../simm.is (talk: public/talks/2026-10-mpi-tuebingen).

## Design aspects (one research note each)

A. Core calculus and its specification (λ vs MC vs Turing categories; effect
   handlers; minimal core forms; spec structure; mechanization in ansatz/Lean;
   katzen/GAT as readable spec).
B. Memory model (values/resources, RC/FBIP, uniqueness, regions, persistent
   DS, fork boundaries, concurrency, per-host realization).
C. Staging and partial evaluation continuum (binding-time grades, runtime
   (re)expansion with invalidation, specialization with guards/deopt, JIT
   tiers, collapse to AOT).
D. Dispatch, polymorphism, hosting and interop (multiple dispatch +
   specialization, protocols, à-la-carte typing, Clojure interop modes,
   platforms).
E. Resources, bounded rationality, learning runtime and physical awareness
   (grades for cost/error, placement/locality, translation functors,
   metareasoning, inference effects, learned optimization with certificates).
