# Entry resolution, ordering and allocation

2026-10-30. The [implemented contract](../../../doc/engineering/candidate-selection.md#live-entry-plans)
retains immutable host-binding plans, checks live Var values, preserves guard
order and corrects direct-site candidate recovery. A fallback collision found
while measuring also motivated bounded four-way entry CodeId slots.

## Comparison scope

[`entry.clj`](../entry.clj) runs three sequential fresh JVMs on one enclosed
accumulator source, with a Long input executing zero loop iterations and a
Double input executing one. Empty, baseline, private and ordered portfolio
caches expose entry overhead; these are deliberately tiny bodies. Both modes
use the same source, candidates, world checks and guard premises. `:reference`
uses the original ordinary guard traversal; `:planned` uses the new traversal
and binding plans. This is a matched mechanism control, not an old-release or
whole-language performance comparison.

Each row warms each mode for 8,192 calls, then measures nine rounds in alternating
mode order. Selector batches contain 512 calls; full-call batches contain 128.
Context bindings occur once per batch outside timing. Full-call comparisons
**disable the direct hook in both modes**, so they isolate ordinary entry. They
include invocation, generated/T0 execution and output, rather than just native
bodies. Startup and preparation are excluded. No elapsed-time assertions,
CPU pinning or frequency control are used. Rows run in a fixed order, so host-JIT
state continues to evolve. These are bounded measurements, not peak-performance
claims. Current-thread CPU and allocated bytes accompany wall time in raw EDN.

Counter instrumentation is separate from timing. For each reached host-root
guard, reference mode resolves a symbol and planned mode checks its retained
binding. Planned mode still reads the live Var; it does not retain truth across
candidates. Resolution counts vary on rejected inputs because each fresh process
may order the guard set differently. Within a matched row the modes preserve the
same order, selected variant and observed value.

Direct and evidence sites have separate current-only observations. Their sources
and interfaces differ, and they have no before control in this study. The direct
selection correction must not be presented as a measured speedup against its old,
incorrect winner cache.

## Final matched results

Medians of the three process medians; wall time in microseconds and allocated
bytes per invocation. Complete per-process ranges, CPU samples and all input
rows are in [`measured/final-summary.edn`](measured/final-summary.edn).

| Ordinary full call | Reference µs | Planned µs | Reference bytes | Planned bytes |
|---|---:|---:|---:|---:|
| Empty cache, Long | 6.89 | 6.81 | 10,553 | 10,553 |
| Baseline, Long | 2.39 | 2.06 | 5,513 | 4,713 |
| Private, Long | 4.59 | 3.25 | 8,689 | 5,585 |
| Portfolio, Long | 3.86 | 2.47 | 8,401 | 5,297 |
| Private guard miss, Double → T0 | 10.40 | 9.05 | 26,761 | 23,769 |
| Portfolio, Double → baseline | 4.60 | 2.96 | 9,377 | 5,617 |

For private Long calls the process-median ranges are 4.35–5.12 µs reference and
2.91–3.40 µs planned. For portfolio Long calls they are 3.81–4.35 µs and
2.28–2.85 µs. These costs include ordinary entry, not the default direct path.

Selector-only private Long medians are 4.00 → 2.04 µs and 4,632 → 1,504 bytes;
portfolio Long is 3.42 → 1.60 µs and 4,608 → 1,480 bytes. The baseline selector
is slightly slower at 2.40 → 2.47 µs despite falling from 1,688 to 864 bytes.
Empty-cache selection is essentially unchanged. These flat/losing rows remain
visible; timing does not improve universally, and selector/full-call medians
from different rows must not be subtracted as additive components.

Separate counters in the successful Long row show five live host guards for
baseline and 26 for private. Reference mode makes that many `requiring-resolve`
calls; planned mode checks that many retained bindings with no resolver call
when the mapping is unchanged. Actual Var reads remain in both modes.

Current-only direct-site process medians are 0.70–1.01 µs / 784 bytes and evidence
site medians are 2.08–2.62 µs / 2,560 bytes. There is no matched old-site speedup
claim. Final process wall times are 4.0–5.5 seconds including launch and the whole
study, versus the anomalous 62.2-second pre-fix process below.

## Identity-cache failure and bounded repair

`pre-collision-fix/` preserves the first longer-warmup cohort. Its third JVM took
62.2 seconds, versus 5.5–5.9 seconds for the others. Interpreted empty-cache and
private-guard-miss calls reached about 1 ms and 4.2 MB allocated per invocation
in that process. These samples remain included; they are not silently discarded.
That process did not record object identities, so attribution of that exact run
remains indirect.

The separate [`entry_collision.clj`](../entry_collision.clj) probe searches at
most 4,096 source instances for a caller/loop pair whose identity hashes share
one entry-cache slot, then measures both cache implementations on the **same
closure terms** in one REPL. The retained [paired sample](collision/repl-paired.edn)
shows 1,031 µs / 4,194,977 bytes with direct mapping versus 5.52 µs / 10,529 bytes
with four ways. This reproduces the mechanism, not a broad language speedup or
controlled peak timing result. Capacity misses remain possible with more than
four active terms sharing a slot. The Core canonical-hash algorithm and its own
cache are unchanged.

The canonical regression uses 513 distinct terms to obtain a collision by the
pigeonhole principle. Alternating the pair must hash each term once, and replacing
the CodeId implementation must invalidate the memoized identity. This correctness
check has no timing threshold.

## Retained cohorts and reproduction

- `before/stage.clj.txt`: source before the entry slice; no old-release timing claim.
- `indexed-before-hints/`: early REPL traversal that reduced allocation but slowed
  elapsed time. Typed persistent-vector access replaced generic indexed access.
  The captured stage/harness hashes match its report. Its per-call context
  bindings differ from the final harness; do not pool these samples.
- `bounded/`: three fresh JVMs with 128 warmups per mode. Allocation improved;
  timing remained sensitive to tiering. The exact harness is retained.
- `pre-collision-fix/`: 8,192-warmup cohort, including the large fallback anomaly,
  and hash-checked stage/test/harness snapshots.
- `collision/`: forced-collision paired REPL diagnostic.
- `measured/`: final source, longer warmup and four-way cache; raw samples, source
  hashes, summary, environment and sequential driver records.

```sh
clojure -J-Xmx1g -J-Xss16m -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' \
  -M -m baseline.entry reproduction-0
```

Outputs go to `target/entry/`. For the forced-collision diagnostic, require
`baseline.entry-collision` in the same classpath REPL and call `run-probe!`.
It writes `target/entry/collision-paired.edn`. The search has a declared limit and
can decline if it finds no suitable identities. Identity hashes are runtime
observations, not a correctness premise of the language.

The fresh standalone and verification suites cover dispatch behavior and the
existing proof models. There is no new universal entry theorem, atomic host
snapshot, automatic promotion policy or general interpreter performance claim.
