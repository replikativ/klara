# Private preparation attribution

2026-10-30. Three sequential fresh JVMs, one fixed source/input family, first-use
attribution and six alternating warm pairs per process. See
[the implemented slice](../../../doc/engineering/preparation-costs.md) and
[the harness](../preparation.clj). Raw records are under `measured/`; `before/`
preserves the relevant source before this slice, not a separately measured
old-compiler baseline.

## Result and comparison scope

Both modes run the same source, consumer, guard and ownership artifact checker,
the same erasure validation and registry-sealed publication. The default mode
produces analysis once. The repeat control adds a second producer execution and
compares the artifacts, then uses the same checker. This isolates repeated work;
it is not a frozen old release comparison or a weaker checking mode.

Per-process medians of six **uninstrumented** warm preparations, milliseconds:

| JVM | Single production + checker | Repeated-production control | Single-mode validation |
|---|---:|---:|---:|
| measured-0 | 27.40 | 32.13 | 3.85 |
| measured-1 | 29.55 | 46.68 | 4.99 |
| measured-2 | 26.30 | 40.77 | 4.43 |

The medians of process preparation medians are 27.4 ms and 40.8 ms. Variation
is substantial, including a 77.7 ms control outlier. This is a small diagnostic
cohort, not a stable speedup or a performance guarantee. Validation was not
optimized by this change; its paired timings remain recorded without a claim
that unrelated variation is a benefit.

The first default preparation took 203–230 ms. Lazy backend resolution/loading
accounted for 98–110 ms of that request. The rest includes first-use compilation,
analysis and host execution effects. These samples exclude starting the JVM and
loading the harness namespaces. Backend initialization is still a real cost;
the warm numbers do not erase it.

Separate traced samples confirm the mechanism in all three JVMs:

| Phase | Single | Repeat |
|---|---:|---:|
| Ownership inference | 1 | 2 |
| Producer ownership check | 1 | 2 |
| Analysis-artifact check | 1 | 1 |
| Artifact ownership verification | 1 | 1 |
| Erasure, including derivation verification | 2 | 2 |
| Original-source relation validation | 1 | 1 |
| Host compilation | 1 | 1 |

The measured source has 51 original Core nodes and 56 owned nodes. Single-mode
funding records 7,571 work units versus 7,681 for the repeat control; both emit
one form of 2,425 bytes. These are admission/work counters, not calibrated CPU
or elapsed-time units. All candidates produced the checked boolean answer and
were actually installed and entered.

## Why no erasure-verdict cache

The broad implementation-root snapshot pilot traversed 39 namespaces and 1,480
Vars. Its per-process median costs were about 1.60, 2.45 and 1.85 ms. The separate
traced erasure validations ranged from about 0.57 to 1.17 ms, with warm REPL
pilots lower still. That does not justify this broad snapshot merely to skip one
small erasure check. The pilot is only a cost measurement: it does not establish
a complete transitive dependency closure, immutable host state or an atomic
snapshot. A more precise cache or a larger region may have different economics.

The implementation therefore retains erasure, source-relation and registry
checks, and targets duplicated production. It does not introduce cross-job
analysis lookup or reuse a prior validation verdict after helper/registry changes.

## Reproduce and interpret

Run these sequentially:

```sh
clojure -J-Xmx1g -J-Xss16m -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.preparation fresh-0
clojure -J-Xmx1g -J-Xss16m -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.preparation fresh-1
clojure -J-Xmx1g -J-Xss16m -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.preparation fresh-2
```

Read `:summary` in each `target/preparation/fresh-N.edn` for the table metrics.
The archived `summary.edn` collects those process medians and attribution counts;
it does not pool calls as independent JVM samples. `driver.json` preserves the
commands, exit codes and whole experiment-process wall times.

Each raw report includes exact source hashes, first-use and warm phase records,
all twelve warm trials, six pair orders, bounded diagnostic drop counts, work,
bytes, emissions, node counts and outputs/cache statistics. The three reports
have identical source hashes. Nested phase durations are inclusive, so do not
sum them as separate costs. Phase collection is enabled only for first-use and
the separate attribution samples; it is disabled for the warm pairs.

No application execution speedup, GPU/LLM cost, retained-class memory or complete
process-startup improvement is claimed. The source/owned/JVM bridges remain
tested, not proved by this measurement. Existing larger-family and fallback
measurements retain their original source cohorts.
