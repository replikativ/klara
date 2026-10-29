# Reproduction and source snapshots

The public source repository is the development environment. A verification artifact
is a frozen source/dependency/data snapshot with commands for its stated
contracts and measurements. Keep these distinct.

## Local verification

A fresh clone needs the Clojure CLI, JDK 25 and network access for the pinned
first-run dependencies. The standalone language/compiler tests do not need
sibling repositories:

```sh
clojure -M:test
clojure -M:verify
```

Verification writes current reports under `target/verification`. Reports name
actual source hashes, theorem/proof receipts, test outcomes and remaining
implementation bridges. The examples include accepted and rejected candidates,
world validity, numerical bounds, private accumulation and guest planning.
Kernel receipt checks do not prove every translator or emitted native function.

The optional integration oracle needs a Wandler checkout at `../wandler` and
its `test-data/init.ndjson` fixture. It is deliberately separate:

```sh
clojure -M:test-integration
```

The staged small-step spec and its T0 differential suite have their own entry
points in [spec/README](../spec/README.md). Record the exact ansatz version or
checkout used. Do not silently substitute a newer local dependency when
reproducing the pinned optimization receipts.

The optional checkout cohort exercised during a recorded verification run was:

| Dependency | Identity | Use |
|---|---|---|
| ansatz Maven | `0.2.115` | Standalone tests and optimization/model receipts |
| ansatz source | `2191c02737cb194d677ff766b4d87948b5c4fb75` | `:spec-diff` and `spec/` tests; separate from the pinned receipt cohort |
| Wandler source | `cf39732cc00b51364b670843a3511d77ae82bf78` | Optional oracle; also needs its external `test-data/init.ndjson` fixture |

Both source checkouts were clean. To reproduce the optional spec cohort, place
ansatz at `../ansatz`, check out the recorded revision and run
`clojure -T:build javac` there before running `clojure -X:spec-diff` here or
`clojure -M:test` inside `spec/`. The pinned Maven version currently fails while
generating the older spec's JVM functions (`Decidable.decide`); this is why the
optional alias is explicit about its source override. It is not a failing
optimization proof or permission to change the standalone kernel silently.

The optional Wandler fixture used here has SHA-256
`91c0b4e96c29e8c6a7b77a71630086601a3588c491ed7f511e971361e3a193d1`.
Wandler's README gives its download instructions. Its fusion benchmark now
lives at `test-integration/klara/fusion_bench.clj`, alongside the oracle;
neither is loaded by the ordinary tests or compiler.

The differential spec corpus has four recorded observation differences, listed
in `test-spec/klara/spec_diff_test.clj`. A passing run checks those expected
differences as well as the agreeing cases; it does not claim universal T0/spec
equivalence.

The recorded source-cohort check also loads every proof in `klara.spec.props` and
runs all 69 reference programs successfully via `clojure -M:test` in `spec/`.
The lookup proof uses distinct query/result binder names and checks both match
branches without relying on their tactic order; its statement is unchanged.

## Claim-to-command map

| Claim/evidence | Command or source | Boundary |
|---|---|---|
| Language/world/authority behavior and executable guide | `clojure -M:test` | Implementation tests, not a full authority theorem |
| Staging and specialization examples/rejections | `clojure -M:verify` | Admitted fragments only |
| ansatz theorem receipts | Verification report and named proof modules | Imported foundation and runtime correspondence assumptions stated |
| Guest planning and policy evolution | `examples/staging/15-planned-jit.klr`, planning tests | Small bounded action graph; cost fixtures are not calibrated forecasts |
| Restricted CEK termination/result | Scalar CEK proof/test modules | Formal restricted machine plus tested T0/encoding boundary |
| Durable deployment | `klara.deploy-test` in the standalone suite | Supported source/Core/data; no continuation or authority cloning |
| Performance measurements | Individual experiment README and frozen raw reports | Use their original sources, workloads and JVM processes; no relabeling old results |

## Release gates

Build a public source snapshot with Python 3:

```sh
python3 scripts/package_artifact.py
```

The archive includes working-tree source, a per-file SHA-256 manifest and the
base Git revision. Its bytes are deterministic for the same source snapshot.
It excludes `.internal/`, local databases, caches and build products. Unpack it
outside the development checkout and run `clojure -Srepro -M:test` and
`clojure -Srepro -M:verify` there. Dependency downloads still require access to
the pinned Maven/Git sources; the archive is not an offline dependency cache.

1. Freeze the scope and claims. Link every claim to a test, theorem or experiment
   and list what remains trusted or unsupported.
2. Run tests and receipts in fresh processes from the candidate source snapshot.
3. Package only intended source, examples, proofs, dependencies and result data.
   Exclude `.internal/`, local databases, temporary files and build products.
4. Unpack elsewhere and follow the instructions from that directory, without
   hidden sibling checkouts or local-only dependency substitutions.
5. Include software/hardware identities, runtime estimates, seeds, expected
   outputs and raw measurements sufficient for each stated contract or result.
6. Archive the final artifact with immutable identity. A mutable GitHub branch
   remains useful for discussion but is not the sole archival reference.

Packaging source does not establish complete compiler correctness, independent
Lean replay or validation of measurements that were not rerun.
