# Persistent accumulator families and entry costs

2026-10-30. One warm Oracle GraalVM REPL cohort, with existing compiler/ownership
code loaded. No production allocation recognizer or native backend was added.
The [runner](../../verification/baseline/ownership_family.clj) uses checked helper exposure followed by the
existing baseline or inferred-owned endpoint, on the same residual Core.
Host Clojure compiles the original source. Differential tests compare the
admitted value, container/element class and failure observations to T0.

## Families

* **Captured update:** two fixed accumulator fields, two snapshot reads/updates,
  and a helper capturing a scalar bias.
* **Branching recurrence:** three cross-dependent fields, two branches/strides
  and a captured update helper. All update RHSs read the previous snapshot.
* **Histogram:** four fixed bins over an immutable input vector. Three explicit
  category comparisons and an “other” bin select literal update slots. This is
  bounded dispatch, not a new dynamic-index ownership rule.

Both helper families use the production bounded composition driver. Ownership
analysis is then freshly run on their residual. Growing `conj` builders and
retained histories are rejection cases. These remain useful targets for later
representations and observation/escape contracts, not accepted examples here.

## Warm full-call results

Each engine/input gets 200 warmup calls, seven rotating samples and ten calls
per sample. Input construction is outside the timed call. Allocation is
current-thread allocation; retained heap, compiler threads and GC attribution
are not measured. The owned histogram includes raw input-layout admission.

At size 10,000, medians are:

| Family | Clojure µs | Generic baseline µs | Owned µs | Baseline bytes | Owned bytes |
|---|---:|---:|---:|---:|---:|
| Captured update | 552 | 788 | 26.8 | 2,235,444 | 9,268 |
| Branching recurrence | 403 | 388 | 113 | 1,677,969 | 9,380 |
| Four-bin histogram | 149 | 137 | 146 | 950,905 | 9,396 |

The numerical families show a substantial whole-call improvement in this
cohort. The histogram shows large allocation savings without a speedup over
the generic baseline. Do not infer universal throughput from allocation alone.
The source has the same four-bin output at each size, so output storage itself
does not grow with the input.

| Family | Baseline bytes at 100 / 1,000 / 10,000 | Owned bytes at 100 / 1,000 / 10,000 |
|---|---|---|
| Captured update | 19,169 / 219,449 / 2,235,444 | 9,268 / 9,268 / 9,268 |
| Branching recurrence | 15,753 / 165,969 / 1,677,969 | 9,380 / 9,380 / 9,380 |
| Histogram | 10,297 / 86,905 / 950,905 | 9,300 / 9,396 / 9,396 |

At size 100 the owned path loses on time for every family. Fixed entry costs
and preparation matter; these measurements do not justify enabling it for all
short programs.

## Preparation and admission

| Family | Helper exposure ms | Baseline preparation ms | Owned preparation ms | Owned validation/install ms |
|---|---:|---:|---:|---:|
| Captured update | 3.62 | 3.25 | 14.68 | 7.75 |
| Branching recurrence | 5.40 | 5.17 | 18.66 | 13.24 |
| Histogram | 2.86 | 5.70 | 24.13 | 18.25 |

These are individual warm preparation observations. They exclude dependency
loading and are not cold-start distributions. The helper-exposure budget
does not meter the separate ownership inference/native preparation. Empty
helper recipes still pay their scan/check costs.

A separate histogram cohort isolates an existing way to reuse input facts.
Issuing identity-bound `:long-vector` evidence for the immutable 10,000-element
input took 43 µs once. The existing fixed unary evidence site then checks the
remaining root/cache/context/host requirements on every call:

| Histogram entry, separate cohort | Median µs | Bytes/call |
|---|---:|---:|
| Generic baseline | 119 | 950,892 |
| Owned, raw input entry | 75.1 | 9,386 |
| Owned, reused evidence entry | 55.9 | 4,770 |

This cohort has different preparation/warmup history: 500 warmups and seven
samples of 20 calls. Its raw-owned time improves too; do not subtract across
the two cohorts to attribute costs. The paired evidence comparison combines
avoiding the element rescan with the fixed worker entry. It does not remove
all admission or isolate just one guard's cost. Evidence issuance must be
charged when reuse is not available. No unsafe unguarded body is timed.

## Correctness and limits

The private observation contract excludes arbitrary host identity. The earlier
[affine composition counterexample](AFFINE-COMPOSITION.md) remains a reason
not to install representation-changing code automatically for every Clojure
context. Each owned candidate here accelerates the separate residual entry;
the production driver only installs its checked local-call chain under the
original entry. A future combined endpoint needs the appropriate observation
contract and source/residual relation, as well as one explicit work budget.

The [ordered-call model](../../doc/engineering/recipe-composition.md) now proves
stateful argument-order equivalence and conditional observation composition.
Fresh-name/Core/CEK/JVM correspondence and the functional-to-owned bridge are
still explicit obligations. These are not Rust/Zig comparisons or a general
automatic affinization result.

[Raw reports](ownership-family-results/) retain every sample, preparation,
representations, receipts and source hashes. `runner-before-evidence.clj.txt`
is the exact earlier runner before the separate evidence helper was appended.
The captured helper source is shared with `affine_composition.clj`; reports pin
that dependency too. Later source changes are separate cohorts.

## Reproduction

```clojure
(require '[baseline.ownership-family :as family])
(family/run-study! "repl-new")
(family/evidence-study! "repl-new")
(require 'baseline.ownership-family-test)
(clojure.test/run-tests 'baseline.ownership-family-test)
;; 2 tests, 50 assertions
```

The family and other composition tests are also included in `clojure -M:verify`.
New reports go under `target/ownership-family/`.
