# Project status

The current Klara implementation is a research prototype. This document is the
current entry point;
numbered implementation reports preserve historical results and assumptions.

| Area | Implemented | Limit |
|---|---|---|
| Worlds | Persistent definition roots, atomic per-world publication, pins, forks and conservative three-way merge | In-memory roots alone are not durable storage; multi-system settlement is not one atomic transaction |
| Definition validity | Source CodeIds and fresh evaluation generations; recorded expansion/value reads | Source identity is not universal runtime-value identity; mutable host state needs a separate contract |
| Staging | Hygienic code values, splicing, running and let insertion | The staged spec covers a smaller language than all hosted T0 behavior |
| Compiler | Guarded JVM paths, direct calls, private arrays, bounded fusion and numerical specialization | General dynamic calls/layouts/effects remain outside these paths |
| Guest optimizer | Bounded pure planning over actual checked recipes; world-editable policy; separate validation/publication | Small action family, supplied cost estimates, synchronous preparation; no general learned or wall-clock-preemptive JIT |
| Speculative pipelining | Online per-site outcome counts, speculative checked follow-up, outcome/basis validation and fallback | Separate host-orchestrated synthetic experiment; no general speculative host-effects sandbox |
| Syntax | Syntax values, local expansion, definition contexts and reusable grammars | Full language descriptors and semantic adequacy interfaces remain proposed |
| Proofs | Scoped staged calculus results and named numerical/private/scalar/driver/CEK/finite-environment model theorems checked by ansatz | Whole T0/compiler/JVM correctness and a complete authority-store theorem are not established |
| Deployment | Versioned source/Core/immutable-data bundles, compatibility checks and fresh-process restore | Captured/pinned closures, live authority, continuations and opaque mutable values decline; no arbitrary heap image |

The [checked-specialization guide](doc/checked-specialization.md) names the
current proof, tested and trusted boundaries. `clojure -M:verify` produces the
current receipt/test report under `target/verification`; it does not replace
historical benchmark reports or establish new performance results.

A release gate is a fresh standalone test run, a fresh verification run, an
artifact built from the reviewed source snapshot, and reproduction from that
artifact. Work in progress must not be described as a verified compiler or
complete compiler verification merely because individual model proofs pass.

Runtime dependencies are Clojure and ansatz. Wandler is an optional differential
oracle sharing the ansatz kernel, not a production compiler service or an
independent proof checker. Datahike/Geschichte storage and further migration of
hosted compiler components into Klara remain later integration steps.

The [engineering index](doc/engineering/README.md) describes runtime contracts,
correctness evidence, measurements and remaining gates.
The [objectives](doc/objectives.md) state the durability, source projection,
provenance and self-hosting goals beyond this prototype.
