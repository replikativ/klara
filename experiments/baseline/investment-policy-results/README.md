# Correctness and bounded investment campaign

2026-10-30. Three sequential fresh JVMs compare four policies on complete finite
application traces, followed by three fresh JVMs rerunning the wider compiler
campaign. The [actual syntax check](../../../doc/engineering/actual-inline-correspondence.md)
and [investment controller](../../../doc/engineering/investment-policy.md) are
implemented; automatic profiling, calibrated learning and a whole-compiler proof
are not. `driver.json` records commands, exits and whole-process wall times.

## Finite-trace result

Each policy has its own world, funding and operational cache. Never prepare,
prepare before the first call, prepare at call eight, and the bounded guest gate
all process the same declared inputs. The gate runs at call eight and at the
layout-shift checkpoint. It may execute extra replay calls; these do not consume
application inputs and their cost stays in its trace. It can stop, prepare,
compare and publish only through the original candidate lifecycle.

Median **whole-trace wall milliseconds** over three processes:

| Trace | Never | Always | Threshold at 8 | Bounded gate |
|---|---:|---:|---:|---:|
| Short helper: 12 calls, zero iterations | 1.25 | 73.19 | 61.00 | 5.41 |
| Hot helper: 1,024 calls, 32 iterations | 227.34 | 27.38 | 30.17 | 45.53 |
| Held-out branching helper: 1,024 calls | 152.12 | 26.90 | 29.32 | 32.23 |
| Hot private accumulator: 1,024 calls | 173.82 | 85.31 | 54.49 | 56.30 |
| Private accumulator with layout shift | 156.58 | 188.52 | 188.11 | 219.40 |

These are individual complete traces per process, not steady-state per-call
medians or confidence intervals. Variation is large: the bounded hot-helper
trace ranges from 36.83 to 48.57 ms; always ranges from 21.95 to 31.69 ms.
All ranges, current-thread CPU, whole-trace allocated bytes, preparation charges,
probe samples and decisions remain in [the summary](measured/summary.edn) and raw
reports. No performance threshold is asserted by a test.

The gate stops without emitting code on all short traces. Its measurement and
policy overhead still makes it slower than never preparing. It installs on the
three longer stable families; it does not consistently beat simpler policies.
In particular the hot helper favors always preparing, and the private family
favors the simple threshold in the median. That is a result to preserve, not a
reason to retune the gate until it wins.

The layout-shift trace starts with 64 Long-input calls and switches to 960
Double-input calls. The private candidate falls back under its ordinary guards.
At the second checkpoint the gate pays for another preparation, then declines
that candidate because it cannot become the active implementation for the new
input. Correct admission does not recover sunk work or automatically retire
the earlier candidate. All optimizing policies lose to never in the median;
the gate is the slowest. A cheap layout prefilter and better horizon/drift
forecasts are future policy opportunities, not implemented successes here.

The branching helper is held out of forecast construction; the fixed forecasts
were not trained on these traces. This is one extra source shape, not a large
held-out evaluation. Advisory estimates are 8 ms for baseline preparation and
30 ms for private preparation, candidate cost fraction 0.5 and safety factor 2.
Those estimates can be badly wrong, especially at first use.

## Measurement boundary

[`investment_policy.clj`](../investment_policy.clj) includes the checkpoint,
source/input admission, extra probes, preparation, validation, publication,
application calls and driver bookkeeping in each trace wall timer. The external
attempt timer includes bookkeeping beyond the controller's individual phase
charges. Failed/declined work remains charged. CPU and allocation counters are
observations, not a runtime allocation guarantee or exact sponsor accounting.

World/bootstrap setup and independent Clojure oracle construction are reported
separately per row. Process launch and harness namespace loading are outside the
traces. In particular, the policy harness preloads the ownership backend before
its traces; it does not demonstrate eliminating cold backend initialization.
Whole-process driver times include launch/loading. The separate wider campaign
below retains first-use backend costs.

Policy order rotates across workloads and processes. Each process runs its
traces sequentially, sharing JVM JIT/GC state; the full experiment is not a set
of isolated cold applications. Probes are short (three samples per phase), and
forecasts assume the current input represents the declared remaining horizon.
No CPU pinning or frequency control was used. These bounded diagnostics cannot
establish a generally optimal policy, peak performance or predictable cold cost.

## Refreshed wider campaign

`campaign/` reruns the unchanged five-family harness against the new production
source. This is a new cohort; older reports remain historical evidence and must
not be pooled with it. Median process warm full-call medians, microseconds:

| Family/input | T0 | Baseline | Private | Portfolio | Clojure control |
|---|---:|---:|---:|---:|---:|
| Helpers, 1,000 iterations | 8,688.82 | 22.24 | — | 48.39 | 42.20 |
| Persistent histogram, 1,000 iterations | 7,285.09 | 97.34 | — | 100.39 | 82.81 |
| Tree worklist, depth 8 | 3,765.65 | 35.57 | — | 39.95 | 26.10 |
| Enclosed accumulator, 1,000 iterations | 4,987.59 | 99.33 | 19.98 | 62.11 | 83.41 |

The private accumulator allocates roughly 9.6 KB per full call versus 223 KB for
baseline, but the portfolio path remains substantially slower than the private
cache alone. Host-JIT call-site behavior, dispatch and the fixed-order harness
remain relevant; these rows do not isolate a cause or prove a compiler
regression/improvement relative to the older cohort. The Clojure controls are
ordinary source compilation under the same harness, not manually tuned Java.

First helper preparation, including bootstrap effects, takes a median 80.5 ms.
The first private preparation takes 215.9 ms, with 14.5 ms validation, while its
baseline preparation is 35.1 ms with 7.3 ms validation. The independent syntax
check remains active; these totals do not isolate its marginal cost from loading,
other validation and host compilation. At the harness's estimated 1,000-call
horizon, private totals 264.7 ms versus baseline 142.1 ms; portfolio totals
383.7 ms. These are estimates using preparation plus measured call components,
not the actual finite-trace measurements in the first table. Escaping-closure
compilation declines in all three JVMs; guard-miss rows remain in the raw data.

## Verification, retained failures and reproduction

The final standalone run passed 302 tests / 7,670 assertions. Verification passed
164 tests / 3,844 assertions, including both new indexed-binding theorems and
source/residual/owned/JVM comparisons. Goal/proof hashes are exported under
`target/verification`. These are model proofs and tested implementation bridges,
not a whole-chain kernel theorem.

`failures/temporary-storage-core.log.txt` retains an earlier failed integration
run with temporary Java-source writes reporting `Disk quota exceeded`, timeouts
and follow-on errors. Its output is incomplete and it is not a validated source
cohort. Clean checks and measurements use an explicit project-local Java temp
directory. `pilot/` retains the earlier REPL diagnostic with intermediate source
hashes; it is not part of the final aggregate. Relevant final source snapshots
are indexed by `source-manifest.json`; raw reports hash all production sources.
`initial/` retains the first fresh-process cohort before the final exception
reporting check; it is not pooled with the final results.

```sh
mkdir -p target/correctness-investment/tmp
clojure -J-Xmx1g -J-Xss16m \
  -J-Djava.io.tmpdir="$PWD/target/correctness-investment/tmp" \
  -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M \
  -m baseline.investment-policy reproduction-0 0
```

Use offsets 1 and 2 for additional fresh processes. For the wider cohort,
substitute `baseline.campaign` and omit the final offset. Reports go to
`target/investment-policy/` and `target/compiler-campaign/`. `summarize.clj`
reconstructs the retained aggregates from the recorded target labels. The final
release gate also builds a frozen source artifact and checks it independently.
