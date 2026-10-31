# Wider persistent-data and call coverage

This is the original measurement cohort. The subsequent
[literal and local-call refinements](REFINEMENTS.md) change literal expansion
and admit nonescaping local calls in validated loops through the optimizing
pipeline. The tables below retain the original sources and declines.

2026-10-30. Three fresh sequential Oracle GraalVM 25 JVMs, 1 GiB maximum heap,
on the same Intel Core Ultra 7 258V machine as the [investment study](INVESTMENT.md).
The [runner](coverage.clj) reuses that study's matched invocation harness:
200 warmup calls per engine/input, nine rotating samples, 100 calls per sample
below input 100 and five otherwise. Preparation is recorded separately.
These are short diagnostic runs, not guaranteed steady-state peak performance.

The programs add map aggregation, materialized records followed by aggregation,
a persistent-list worklist over an immutable tree, and a locally bound callback.
All admitted timed engines check the same results against Clojure. Unsupported
engines are absent rather than replaced with T0. Allocation covers the current
thread, including invocation; retained heap and compiler threads are not measured.

Ranges below are process medians, microseconds per full invocation:

| Program/input | Clojure | SCI 0.15.59 | T0 | Baseline | Existing optimizing |
|---|---:|---:|---:|---:|---:|
| Histogram, 10,000 items/32 buckets | 654–1,562 | 933–1,717 | 27,610–51,729 | 682–1,567 | 942–1,805 |
| Build and aggregate 5,000 records | 565–741 | 1,406–1,720 | 38,079–49,399 | 999–1,167 | 1,150–2,014 |
| Tree worklist, depth 12/4,096 leaves | 132–165 | 697–814 | 33,975–34,456 | 143–147 | 190–209 |
| Local score callback, 10,000 items | 7.43–7.63 | 330–389 | 21,998–40,001 | Declines | Declines |

The broad histogram range illustrates process variability; compare paired raw
rows rather than dividing unrelated endpoints. Histogram and tree baseline
allocation is close to Clojure. Records show a real allocation difference:
baseline about 3.66 MB/call, versus 2.33 MB for Clojure. Native loop emission
helps these persistent programs, but does not solve all collection costs.
The optimizing path also records deoptimization/feedback activity; a zero
fallback count must not be interpreted as proof of entirely native execution.

## Record constructor control

Dynamic map literals expand to Klara's `hash-map` primitive. Host Clojure uses
`PersistentArrayMap` for the two-field record; T0 uses `PersistentHashMap` for
that dynamic literal. Fully constant map literals can instead remain quoted
values, so the distinction must be checked on the dynamic expression.

The [constructor control](constructors.clj) changes only nonempty map literals
in the Clojure source to explicit `hash-map` calls. It asserts that the two
forms expand to exactly the same Klara CoreID. Three further fresh processes
use 500 rotating warmup calls and nine batches of 20 at 5,000 records:

| Variant | Time µs | Current-thread bytes/call |
|---|---:|---:|
| Clojure literal records | 392–502 | 2.33–2.42 MB |
| Clojure explicit `hash-map` | 611–649 | 3.65 MB |
| Klara baseline | 627–732 | 3.66–3.77 MB |

This accounts for much of the gap in that paired cohort. It is a separate
warmup/source cohort from the table above; do not subtract the two tables to
estimate a component cost. Changing Klara's collection representation is not
automatically a valid native optimization: host class observations can expose
it. Better literal compatibility or an unobservable internal representation
rewrite needs an explicit semantic/escape contract. No such change is made here.

## Mutual calls: capability, not throughput

All three processes separately run a two-function `letfn` even/odd program at
64 and 10,000 tail transfers. T0 and both private experimental machines return
the expected result at both sizes. Both compiled paths decline the recursive
group. Host Clojure and published SCI succeed at 64 and hit JVM stack overflow
at 10,000 in these runs; SCI wraps its failure. Those outcomes are recorded
as failures, not timings. This does not describe the local forkable SCI branch.

T0 has proper mutual-tail execution through its explicit continuation machine;
total allocation is not constant just because live continuation depth is
bounded. General native mutual tail calls require a dispatch loop/trampoline,
ordered argument transfers and validity/recovery contracts. Emitting ordinary
recursive JVM calls would change Klara's bounded-stack behavior.

## What the evidence prioritizes

Local callable closures and recursive call groups are now explicit coverage
gaps, not merely slow native loops. Closed local calls/inlining and a checked
recursive-call ABI should follow the shared source/generator correctness work.
The record control independently identifies representation/constructor cost.
These motivate shared call, shape and observability facts rather than another
arithmetic-loop recognizer or an unconditional extra optimization pass.

The [Code interface](../../doc/engineering/code-views.md) provides read-only
binding/control descriptions and scope-checked reconstruction as a first
foundation for those analyses. It does not already implement a closure inliner,
native mutual recursion or a universal staged compiler proof.

## Reproduction and provenance

```sh
for process in 0 1 2; do
  clojure -J-Xmx1g -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"] :deps {org.babashka/sci {:mvn/version "0.15.59"}}}' \
    -M -m baseline.coverage "$process"
done
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.coverage-summary
```

Use the same process command with `baseline.constructors` for the constructor
control. [Raw reports and summary](coverage-results/) pin sources and JVM
arguments. The summary refuses mixed main cohorts. Constructor results are a
separate source cohort: read-only binding labels were added to the unused Code
inspection helper after the main runs. Its earlier measured source is preserved
under `coverage-results/source/`; it does not participate in these workloads.
Timing programs and inputs are otherwise unchanged. New runs go under `target/`.
