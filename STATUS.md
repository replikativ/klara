# Project status

The current Klara implementation is a research prototype. This document is the
current entry point;
numbered implementation reports preserve historical results and assumptions.

| Area | Implemented | Limit |
|---|---|---|
| Worlds | Persistent definition roots, atomic per-world publication, pins, forks and conservative three-way merge | In-memory roots alone are not durable storage; multi-system settlement is not one atomic transaction |
| Definition validity | Source CodeIds and fresh evaluation generations; recorded expansion/value reads | Source identity is not universal runtime-value identity; mutable host state needs a separate contract |
| Staging | Hygienic code values, splicing, running, let insertion, bounded Code views and fresh ordered template composition | Correspondence proofs and full module/phase binding semantics remain open; the spec covers a smaller language |
| Compiler | Guarded JVM paths, direct calls, private arrays, bounded fusion, nonescaping local calls in validated loops and numerical specialization | Escaping closures and mutually recursive native groups still decline; broader layouts/effects remain open |
| Baseline preparation | Opt-in compiler with direct-loop lowering, bounded jobs, named priority variants, closed-Code preparation, world-managed services, opaque checked local-call edges and funded strategies and an enclosed boolean-consumer owned endpoint under one budget | Edited services remain stepped; general heterogeneous recipe/fact composition, initializer acceleration, automatic profiling and persistent native artifacts remain open |
| Guest optimizer | Bounded pure planning over actual checked recipes; world-editable policy; caller-driven fixed/threshold scheduling and explicit funded measured checkpoints; separate validation/publication | Fixed experimental observation projections; small action family, supplied cost estimates, synchronous preparation; no general learned or wall-clock-preemptive JIT |
| Speculative pipelining | Online per-site outcome counts, speculative checked follow-up, outcome/basis validation and fallback | Separate host-orchestrated synthetic experiment; no general speculative host-effects sandbox |
| Syntax | Syntax values, local expansion, definition contexts and reusable grammars | Full language descriptors and semantic adequacy interfaces remain proposed |
| Source/tooling | Guest nREPL, `.clj`/`.cljc` loading, world-managed names and explicit require aliases | Bounded `ns` subset; host reader scaffolding and trusted interop; ordinary host atoms remain shared |
| Proofs | Scoped staging and numerical/private/scalar/driver/CEK models, plus stateful ordered-call and conditional observation-composition theorems checked by ansatz | Whole T0/compiler/JVM correctness, fresh-name correspondence and a complete authority-store theorem are not established |
| Deployment | Versioned source/Core/immutable-data bundles, compatibility checks and fresh-process restore | Captured/pinned closures, live authority, continuations and opaque mutable values decline; no arbitrary heap image |

The [checked-specialization guide](doc/checked-specialization.md) names the
current proof, tested and trusted boundaries. `clojure -M:verify` produces the
current receipt/test report under `target/verification`; it does not replace
historical benchmark reports or establish new performance results.

The [staged baseline implementation](doc/engineering/compiler.md#consolidated-implementation-boundaries)
records current options, explicit compatibility adapters and accounting.
The current campaign prioritizes checked staging composition, JVM performance and focused correctness;
native bootstrap work is deferred. Allocation removal through ownership and
representation analysis is a showcase family with an explicit observation
boundary, not a general Clojure/Rust performance claim.
The [funded strategy implementation](doc/engineering/preparation-strategies.md)
records separate policy/reference roots, normalized outcomes and an admitted
pure fork-benchmark experiment. Timing evidence is separate from correctness;
arbitrary host-memory isolation and automatic candidate promotion remain open.
The [enclosed private endpoint](doc/engineering/private-accumulator.md) links
inlining and owned lowering to the original entry; its boundary and implementation
bridges remain restricted and tested.
The [candidate-selection milestone](doc/engineering/candidate-selection.md) adds
stable priority slots and original-source reconstruction. Four
[enclosed-consumer model theorems](doc/engineering/private-accumulator.md#enclosed-consumer-correspondence) and
tested multi-stage bridges strengthen the correctness ledger. The
[wider JVM campaign](experiments/baseline/campaign-results/README.md) records
three fresh processes, preparation/validation costs, allocation, declines and
portfolio overhead; first-use investment remains expensive.
The [first preparation-cost slice](doc/engineering/preparation-costs.md) now
produces private analysis once and checks a candidate-local artifact, with phase
attribution and paired controls. Erasure and registry checks remain active;
further preparation and correspondence work remains on the campaign.
The [entry-plan slice](doc/engineering/candidate-selection.md#live-entry-plans) now retains immutable host
binding plans while checking Var values live and fixes direct-site preferred
candidate/miss recovery. Four-way identity slots address a reproduced CodeId
cache collision cliff in fallback. [Matched measurements](experiments/baseline/entry-results/README.md)
separate ordinary guard traversal from current-only direct/evidence observations.
Opaque predicates retain their evaluation order.
The [actual inline correspondence slice](doc/engineering/actual-inline-correspondence.md)
adds an independent indexed check and two lexical model proofs; full implementation
correspondence remains open. The [bounded investment checkpoint](doc/engineering/investment-policy.md)
now measures, prepares and publishes through the existing lifecycle. Its
[finite traces and refreshed campaign](experiments/baseline/investment-policy-results/README.md)
retain short/shift losses and cold/portfolio costs. Architecture/documentation
consolidation is complete; general phase-aware linking and stronger actual
Core/owned/JVM correspondence remain open. No general automatic JIT is claimed.
The [compiler architecture](doc/engineering/compiler.md) explains which parts
are hosted, written in Klara, staged, independently checked and world-managed.
The [Code-view milestone](doc/engineering/code-views.md) adds guest structural
generators and fresh ordered template composition.
[Wider measurements](experiments/baseline/COVERAGE.md) expose call and constructor
gaps alongside fast persistent loops; the subsequent
[refinements](experiments/baseline/REFINEMENTS.md) address map literals and
nonescaping local calls. Compiled mutual recursion remains open.
The [investment study](experiments/baseline/INVESTMENT.md) compares compiled
execution to SCI on identical inputs and separates primitive bodies, installed
entry and preparation costs.

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

The [consolidated layout](doc/engineering/codebase-map.md) separates
maintained verification from historical experiments, uses explicit compiler
dispatch, and adds caller-driven fixed/threshold scheduling around one job.
Unsupported world-dependent pinned closure lifting now rejects conservatively;
general phase-aware linking remains open. The release gate runs both `:test`
and `:verify`; neither replaces the other.
