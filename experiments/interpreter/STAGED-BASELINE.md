# Mandatory baseline: first matched diagnostic

2026-10-30, three fresh sequential JVMs, Oracle GraalVM 25.0.1+8.1 on the
local development machine. These are default host-VM measurements, not C2
measurements. [Source hashes and raw runs](staged-baseline-results/) pin the
cohort (`sources.txt`). The `.edn` files contain unchanged result maps.
Optional checkout-only `.stdout` files additionally retain JVM startup warnings.

The [implemented path](../../doc/engineering/compiler.md#consolidated-implementation-boundaries)
removes optional compiler passes and emits generic bodies. This diagnostic
compares full `ev/run` calls of an already expanded call expression under the
same immutable root, using an empty cache for T0 and an installed baseline
cache. It includes stage admission and call context, not only emitted bodies.
Source parsing/definition evaluation is outside preparation and call timing.

Each case has 200 warmup calls per engine, then seven samples of 100 calls,
alternating measurement order. The table gives the median of the three
per-process sample medians. These short runs do not establish a fully warmed
steady state or statistical confidence intervals.

| Case | Preparation ms | Validation/install ms | T0 full call µs | Baseline full call µs |
|---|---:|---:|---:|---:|
| Tiny `(+ x 1)` | 14.79 | 1.78 | 10.76 | 11.58 |
| Branchy `let`/arithmetic | 8.46 | 1.37 | 13.07 | 9.90 |
| 64-step vector-state recurrence | 24.47 | 0.36 | 291.91 | 13.63 |
| Guest transfer producer, three destinations | 5.68 | 0.49 | 67.28 | 15.91 |
| Two calls to one acyclic helper | 10.97 | 0.63 | 24.75 | 17.10 |
| Unsupported staging body | 0.64 | — | — | — |

Compiler namespace loading is separate: 1307, 1199 and 1255 ms. The recurrence
is the first loop and pays for compiling the reviewed guest transfer service;
its budget records two emissions. Later loops reuse that service. The acyclic
case emits/installs both subject and its one helper. The tiny function loses
in all three process medians, and preparation does not amortize for short runs.
This evidence supports an opt-in bounded policy, not universal compilation of
every definition or a faster end-to-end startup claim.

All five admitted cases installed successfully in all processes, with zero
deopts and zero fallbacks in the recorded runs. Both loop cases record
`:producer :klara-baseline` and the producer CodeID in their actual emission
receipts. Stage hits count admission events: direct-selection memo hits do not
increment that counter on every native call. The unsupported staging case
declined after three charged work units and emitted nothing.

An early call is also recorded after the initial equality check; it is **not**
the first cold invocation. These samples vary considerably (for example the
acyclic case ranges from 41 to 130 µs). Raw samples preserve that variability.
No source-specific proof search, scalar Java compilation, persistent native
artifact, adaptive profile policy or private initializer cache participates.

Reproduce from the repository root, without competing timing workloads:

```sh
mkdir -p target/staged-baseline
for run in 1 2 3; do
  clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M \
    -m interpreter.staged-baseline-bench > "target/staged-baseline/run-${run}.stdout"
done
```

Correctness checks for this implementation: full core 219 tests/6834 assertions
and verification 141/3490 passed before the final tooling/aggregate-literal
hardening. Focused baseline/load/transcript/driver checks afterward passed
22/569; optional nREPL passed 1/8 with loopback networking enabled. The final
baseline-only check passed 10 tests/78 assertions, including an additional
aggregate-literal regression.
These remain tests and diagnostic measurements, not whole-compiler proofs.
