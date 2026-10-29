# Consolidation: accepted and rejected specialization

For a fresh verification run:

```sh
clojure -M:verify
```

Current reports go to `target/verification/`, including `evidence.edn`, scalar
execution witnesses and the live planning/deployment example. Checked-in
benchmark and evidence files below preserve their historical source snapshots.

Start one persistent REPL at the repository root:

```sh
clojure -Sdeps '{:paths ["src" "test" "experiments" "experiments/proof_staging"]}' -M
```

```clojure
(require '[consolidation.run :as run])
(run/verify!)
```

This runs targeted implementation/lifecycle suites, kernel-model tests and
counterexamples, then writes `target/verification/evidence.edn`. Proof reports identify the exact
goal/proof hashes, independent checks and trusted imported Init statements.
There is no dependency override and no JVM restart per proof or candidate.

The executable examples are `examples/staging/09-checked-composition.klr` and
`10-compositional-accumulator.klr`. The former first loads the scalar/traversal
builders in `experiments/proof_staging/polynomial.klr`. The test suite exercises
the same fork/prepare/install path directly. Unknown recipes and failed proofs
decline without publication; out-of-domain calls run the original source.

`examples/staging/11-proof-bearing-accumulator.klr` extends example10 with
`:stage/prepare-affine-proved`. `helper_bridge.clj` and `source_model.clj` construct
kernel goals from original helper/caller-step syntax, preserving binders and
calls. `proved_accumulator.clj` validates these contracts and their private-model
composition before installing the existing native array executor. Proof bootstrap
runs at adapter load; candidate jobs only use the captured Env. Scalar and vector
helper contracts are distinguished, and a valid callee proof does not admit a
wrong call-site argument. See [correctness ledger](../../doc/engineering/correctness.md) for the exact
scope and remaining trusted reifier/T0/eraser boundaries.
Admission also binds the actual owned endpoint and checks its callback equation;
an affine-valid double increment is rejected as semantically incorrect.

`examples/staging/12-native-composition.klr` composes numeric and fusion steps
with `:executor :private-array`. The actual final fold is lowered through shared
`compile/strict_fold.clj`, `compile/updates.clj` and the ownership compiler;
there is no statistics-specific backend. Both pass orders are checked.
`fold_model.clj` supplies a partial-fold/private-cell simulation, total-fold
correspondence, sum bound and an actual-endpoint composition proof. A generated
two-slot count/sum fold uses the same compiler with tested evidence. See
[correctness ledger](../../doc/engineering/correctness.md) for exact limitations.

`private_state.clj` proves a simulation of finite scalar-cell plans, with ordinary
failure categories, alias steps, branch safety and immutable outside frames. A
proof-producing checker rejects retained versions. Host model interpreters are
handwritten; singleton-loop tests check their correspondence to T0, owned
reference execution and guarded primitive execution. This is not a formal
extraction proof or a theorem for all accepted Clojure programs. In particular,
the ansatz generated JVM model functions are not used as an execution oracle.

`interval.clj` proves monotonicity and intermediate capacity safety for
nonnegative +/* trees. Its per-expression kernel proofs include partial n-ary
products. `boundChecked` is an all-intermediates-fit model; the theorem covers
successful bounded evaluation, not the timing/order of overflowing executions.
The capacity product for fold size is checked, while the complete operational
List-fold/Long bridge remains separate. No signed reassociation is justified.

The default mathematical pipeline retains its tested T0 vector executor;
`:private-array` selects the new native path. Private accumulation uses a typed
setter and computes snapshot RHSs before stores. Count's Integer result remains
distinct from Long. The predictor rerun is `../adaptive_affine/predictor-s28-results.edn`;
the original report is preserved and should not be mixed with it.

Independent-process pilot (run sequentially, without concurrent tests):

```sh
clojure -J-Xmx1g -Sdeps '{:paths ["src" "test" "experiments" "experiments/proof_staging"]}' -M -m consolidation.benchmark 7
clojure -J-Xmx1g -Sdeps '{:paths ["src" "test" "experiments" "experiments/proof_staging"]}' -M -m consolidation.benchmark 8
clojure -J-Xmx1g -Sdeps '{:paths ["src" "test" "experiments" "experiments/proof_staging"]}' -M -m consolidation.benchmark 9
```

In the REPL:

```clojure
(require '[consolidation.benchmark :as bench])
(bench/summarize! [7 8 9])
```

[The report](benchmark-summary.md) labels variability,
warmup, allocations, preparation, losing policies and earlier development runs.
This is a one-family pilot, not a publication-quality benchmark corpus.
`native-residual-7.clj.txt`, `native-entry.javap.txt` and `native-loop.javap.txt`
show the generated representation. The entry dump omits its large static
constant initializer. The loop dump includes primitive arithmetic descriptors
and typed array access; the Clojure compiler still emits a per-invocation closure.

The broader 17-case manifest in `cases.edn` is the plan's coverage inventory,
not a claim that all cases have new integrated tests. Current new cases cover
aliases, helpers, retention/path joins, world dependency changes, late reads,
effects, tampering, failed proof publication, inert domain admission and private
cleanup. Scope/authority/recovery suites retain their existing scope; universal
scope freshness and interior owned recovery remain open.

See [the consolidated account](../../doc/checked-specialization.md) and
[correctness ledger](../../doc/engineering/correctness.md) before interpreting the receipts;
S26/S27 retain their historical narrower scopes and measurements.

S29 adds [producer/consumer fact transport](../../doc/engineering/correctness.md),
the actual staged [example13](../../examples/staging/13-producer-consumer.klr)
and `producer_model.clj` / `producer_consumer.clj`. A producer exports an opaque
identity-bound fact; consumers discharge input guards without rescanning. A
known pure batch admits once and uses a fixed unary worker, with a primitive
return ABI for numeric consumers. Context misses return a call plan so ordinary
Klara code performs fallback in the original continuation.

`staged/prevalidate` checks an immutable executable in preparation and seals an
opaque receipt. Publication reuses it after current world/fork checks; changed
executables or checker registries invalidate the receipt. Mathematical/native
composition now transports the native worker's host dependencies too. S28 raw
timings remain historical, preceding this repair.

For the admission pilot, run `consolidation.admission-benchmark` with the same
classpath/heap as above, sequentially for IDs 6, 7 and 8; then call
`consolidation.admission-benchmark/summarize! [6 7 8]` in the REPL. The
[report](admission-summary.md) separates existing evidence, its initial scan,
producer materialization, pure batch amortization and validation/publication.
Raw samples and the non-additive guard instrumentation are retained. Early
admission processes are development diagnostics, not the final aggregate.


S30 adds `14-demand-and-await.klr`: finite map/take/sum specialization with
whole-vector totality bounds, and lexical T0 suspension between native calls.
`demand_model.clj` contributes four independently checked theorem receipts;
`demand-example.edn` records actual source/target/lowered/owned terms, and
`suspension-trace.edn` records pinned-world resumption and live lease settlement. Rejection
tests include lazy chunk errors, eager tail errors and tampered evidence.
The operational observer's pending result is not a source error. See
[correctness ledger](../../doc/engineering/correctness.md) and the
[correctness ledger](../../doc/engineering/correctness.md).

Canonical CodeId format is now v1: quoted numeric representations are distinct,
and memoization is keyed by term identity. Rebuild generated IDs and prepared
artifacts after this change. Existing benchmark reports are historical reports
with their original identities, not measurements of the S30 sources. S30 makes
no new performance claim. General hosted literal adequacy and the restricted
Core/model/JVM correspondence proof remain open.


S31's `scalar_core.clj`, `scalar_driver.clj`, `scalar_sum.clj` and
`counted_core.clj` add original-syntax scalar bounds, an indexed-prefix driver
proof, and a discharged reachable sum invariant. The REPL test entry is:

```clojure
(require 'consolidation.scalar-core-test)
(clojure.test/run-tests 'consolidation.scalar-core-test)
```

The full runner includes these tests and exports `correspondence-example.edn`.
It records 38 independently checked theorem receipts in total. General callbacks
retain an explicit reachable-safety premise; the concrete +/zero consumer proves
it from element/count bounds. Core decoding, finite-value encoding, T0 CEK and
JVM/owned backend correspondence remain stated bridges. See
[correctness ledger](../../doc/engineering/correctness.md). New proofs use the pinned dependency;
no kernel-generated JVM model functions serve as differential oracles.

The separate world-management exploration is runnable in the same REPL:

```clojure
(require '[consolidation.world-evolution :as evolution])
(evolution/run-experiment!)
```

It branches a guest compiler policy, merges it through branchable authority,
checks retained old closure behavior and replays one closed source form in a
fresh in-memory world. It also checks the source/Core gap of raw runtime-value
definitions. This is not added to the S31 theorem/test counts and does not claim
proof-gated definition merging, durable state or process checkpointing. See the
[correctness ledger](../../doc/engineering/correctness.md).
