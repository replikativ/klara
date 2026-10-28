# Klara

Klara is a Lisp for **forkable, inspectable computation**: simulation,
inference and certified optimization. It reads Clojure syntax, is hosted on
the JVM and embedded in the Clojure ecosystem (Klara closures are Clojure
functions, Clojure functions are callable from Klara), but its design is
not JVM-only: a small host contract separates the portable language from
the substrate. Named after Klára Dán von Neumann, who wrote the code for
the first computerized Monte Carlo simulations on ENIAC in 1948.

What makes it different from Clojure:

- **Programs live in a world**, an immutable versioned map of definitions.
  Redefining something publishes a new version; running code keeps the
  version it started with until it explicitly moves on; the world can be
  **forked** to try an edit or run a counterfactual without disturbing the
  original.
- **Effects are first-class**: inference (`choose`/`observe`), generators,
  exceptions, world and host access are operations performed on handlers,
  so the same model runs under exact enumeration or a particle filter.
- **Meaning is fixed, speed is negotiable**: a small core with a
  kernel-checked small-step semantics defines what programs mean;
  optimized code is a cache entry with guards and a certificate saying why
  it agrees with the original.

## Status

**Research prototype, private draft.** What runs today, on Clojure 1.12:

- the expander (Clojure syntax → 12 core forms, hygienic, with recorded
  world reads), worlds with versioned publication, forks and pinned fibers,
  and **T0**, a reference interpreter with lexical and dynamic effect
  handlers (S1);
- an explicit, guarded Clojure compiling tier for a conservative subset,
  with tested inlining, scalar replacement and lexical tail/abort handlers (S8);
- a REPL whose transcripts in this repository are tests;
- staged code values (`code`/`esc`/`run`/`lift`, let-insertion);
- one certified optimization: map/filter/reduce fusion proved in the
  [ansatz](https://github.com/replikativ/ansatz) kernel (S3);
- authorities and forks (RFC 0001) enforced dynamically in T0: authority
  tokens in a store, the `fork` form with `adopt!`, settlement that fails
  closed, fork-resume admission, deferred irreversible effects (S6);
- the generator-independent parts of a compiling tier (S7): executable
  validity checked once per basis root, speculative executables whose
  guards inside the body deopt to T0 from frame states (effects already
  performed are not repeated), deopt feedback keyed by (CodeId, site);
- the formal small-step semantics of the core in ansatz, with determinism,
  progress, preservation of scoping and the s-m-n law proved (`spec/`).

What is **design only**: the static affine layer and `fork-following` of
RFC 0001, authorities in the formal semantics, effect
general compiled effect handling (RFC 0002), full T1/T2 coverage and unboxed
layouts, the predictor ladder, adequacy
of a denotational model, and hosts other than the JVM. The guide marks
every such feature where it comes up.

## Quick start

Requires the Clojure CLI and a recent JDK (developed on JDK 25). The test alias also expects a
checkout of [wandler](https://github.com/replikativ/wandler) next to this
repository (`../wandler`) for one differential test.

```
clojure -M:repl                       # the Klara REPL (prompt k=>; :repl/help lists commands)
clojure -X:test                       # all tests, including every transcript in doc/guide and examples
echo '(handle [m {:choose (fn [p k] (concat (k true) (k false)))}] [(perform m :choose 1/2)])' \
  | clojure -M:repl                   # a first example: a handler that enumerates both choices
```

Then read `doc/guide/01-core.md`.

## Map of the repository

| Path | What it is |
|---|---|
| [`doc/guide/`](doc/guide/README.md) | **start here**: the language through runnable examples, chapter by chapter |
| [`examples/`](examples/README.md) | worked examples with tested transcripts (SMC, coupled forks, basis raise, certified fusion, staging) |
| [`doc/semantics.md`](doc/semantics.md) | the formal semantics in readable form: rules, stuck states, what is proved |
| [`doc/architecture.md`](doc/architecture.md) | how Klara is built: pipeline, host contract, tiers, compiler as values, commuting squares |
| [`rfc/`](rfc/) | design proposals: 0001 forks and authority, 0002 effects and handlers |
| [`spec/`](spec/README.md) | the kernel-checked small-step semantics in ansatz, and its proofs |
| `src/klara/` | the implementation: `core` (12 forms), `expand`, `world`, `defs`, `eval` (T0), `stage` (cache), `fusion` (S3), `code` (staging), `repl` |
| `test/klara/` | tests, including the transcript harness |
| [`experiments/`](experiments/) | measurements behind design decisions (JVM effect-handler costs, a Klara map) |
| [`doc/background/`](doc/background/README.md) | history: design iterations, research notes, reviews, implementation reports S1 and S3 |

## Design principles

1. **Value semantics and code as data**, on a Lisp foundation with Clojure
   syntax; the running system is the development environment.
2. **Sound by design**: a formally specified core (kernel-checked in
   ansatz, kept Lean-4-shaped); host quirks are tolerated only at the
   interop boundary, named and tested, never adopted into Klara's own laws.
3. **Forkable worlds**: definitions are versioned values, code runs against
   a pinned basis, and data is shared while authority (resources, evidence,
   budgets, random streams) is split, never duplicated.
4. **Features à la carte**: an untyped core with opt-in narrowing layers
   (shape claims, proofs); annotations reject programs or license faster
   representations, but never change a successful result.
5. **Staging as a continuum**: expansion, specialization and
   re-optimization happen at any time, as guarded caches with certificates;
   deleting every cache changes no result.

## License and clean room

Licensed under the Apache License 2.0 (`LICENSE`). Klara is written
clean-room with respect to Clojure's implementation: Clojure is used only
as an unmodified dependency through its public API, and no Clojure Java
sources were consulted when writing the runtime
(`doc/background/00-design-space.md`, "Copyright separate"). Klara is part
of the [replikativ](https://replikativ.org) stack; its calculus is λ∨,
developed separately.
