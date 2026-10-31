# JVM families, candidate portfolios and investment costs

2026-10-30. Three sequential fresh JVM cohorts, fixed source/input families,
and seven rotating warm rounds per input. This is a bounded diagnostic study,
not a peak-performance evaluation or a calibrated autonomous investment policy.
The [harness](../campaign.clj), [summary generator](../campaign_summary.clj),
[raw measured reports](measured/) and driver process records are retained.

## Matched programs and results

All engines receive the same source and inputs. Baseline preparation explicitly
inlines admitted local helpers. The private variant adds the enclosed owned
endpoint. The portfolio installs both under named priorities, checks runtime
eligibility, and falls back through the ordinary entry mechanism. The Clojure
control compiles the same functional source with checked arithmetic; it does
not receive the private rewrite.

The table gives medians of the three process warm medians, in microseconds per
call. Full ranges and raw samples remain in `measured/summary.edn` and its inputs.

| Family / input | T0 | Baseline | Private only | Portfolio | Clojure |
|---|---:|---:|---:|---:|---:|
| Helper polynomial, n=1000 | 6604 | 16.1 | — | 32.3 | 34.6 |
| Persistent histogram, n=1000 | 7221 | 99.0 | — | 99.9 | 87.5 |
| Tree worklist, depth=8 | 3558 | 39.2 | — | 46.8 | 26.7 |
| Enclosed accumulator, n=1000 | 4275 | 76.1 | 23.7 | 50.9 | 69.0 |
| Enclosed accumulator, n=16.5 | 81.8 | 5.36 | 86.4 | 13.9 | 2.17 |
| Escaping closure creation, n=1000 | 3.16 | 3.09 (decline) | — | 3.27 (decline) | 0.326 |

The private loop's full-call allocated bytes fell from about 223 KB baseline
to 12.3 KB at n=1000. This includes entry/harness allocation, not just the array
body. Its warm-time process range was 14.2–30.6 microseconds; the portfolio
range was 28.2–93.0 microseconds. Do not infer a stable speedup from the central
values or assume a portfolio is as cheap as a single installed candidate.

`measured/prepare.clj.txt` preserves the preparation helper at measurement time.
The current helper additionally rejects malformed selection options when a
startup job is constructed. This does not change the benchmark's direct funded
request path; the snapshot retains the exact earlier hash rather than relabeling
the raw cohort as a measurement of later source.

For Double n=16.5, the private-only cache rejects its Long premise and uses T0.
The portfolio instead selects the generic baseline. The result remains exact,
but searching the richer candidate set costs more than the baseline-only path.
The closure-producing program declines in every process. Its timed operation
is closure creation; calls on that returned closure are correctness probes
outside timing, not included execution costs.

## Preparation can dominate

Median preparation costs were approximately 98.8 ms for the first helper
fixture, 13.6 ms for the histogram, 17.7 ms for the worklist, 22.7 ms for the
generic accumulator, and 191 ms for its private variant. Validation and
installation are separate recorded phases. The first fixture includes cold
compiler/bootstrap work; fixtures run in fixed order, so these are not paired
estimates of an order-independent compiler cost. A closure decline still costs
roughly 0.65 ms and retains its work charges.

For the accumulator at n=1000, an estimated 1000-call horizon costs about
102 ms for baseline, 213 ms for private only, and 258 ms for the portfolio,
including the corresponding preparation/validation/publication phases. The
faster private body does not repay that initial investment relative to baseline
within this horizon. These are per-process estimates composed from measured
phases and warm medians, not observed 1000-call end-to-end traces. They illustrate
why correctness admission and priority are insufficient investment policies.

Each fixture uses one Funding object across preparation variants. Portfolio
publication renews an earlier validation receipt when loading the ownership
backend changed the checker registry. Every measured cohort exercised one such
renewal, and its cost belongs to portfolio publication. Existing installed
candidates and stale receipts are distinct; the latter are not silently trusted.

## Measurement scope and corrections

Wall time, current-thread CPU and current-thread allocated bytes are recorded
for preparation, validation, installation, first-observed calls and warm calls.
First-observed is not cold-JVM latency: an oracle runs before timing, previous
inputs warm the same engines, and namespaces/runtime dependencies are already
loaded. Clojure source compilation is measured separately. Source/world setup
is reported as `:load-ns`, outside finite-horizon estimates. Background JIT/GC
CPU, retained code/class-loader memory and full application startup are not
attributed to individual calls. The driver records whole experiment-process
wall time, which includes benchmark work and is not application startup time.

The common invocation/binding/volatile-sink harness is included; its noop
measurement is reported and not subtracted. Small inputs batch eight calls;
larger inputs batch one. Eight warmups and seven measured rounds are too short
to assert C2 steady state. Training, exploration and autonomous scheduling are
absent. No elapsed-time assertions enter the test suite.

The first fresh run failed closed on a stale validation receipt; its driver
record and failure text are preserved. `instrumentation-before/` preserves
three preliminary cohorts whose CPU accessor used reflective host calls. Those
calls added substantial measurement overhead, especially at batch one. The
measured cohort fixes the accessor with a typed interface and precomputed
availability checks. Do not merge the preliminary measurements into the table.

## Reproduction

```sh
python3 scripts/run_compiler_campaign.py --label fresh --processes 3
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.campaign-summary target/compiler-campaign/fresh-summary.edn target/compiler-campaign/fresh-0.edn target/compiler-campaign/fresh-1.edn target/compiler-campaign/fresh-2.edn
```

The summary checks that the three input reports share the same source hashes.
It retains min/median/max of process medians rather than pooling calls as
independent samples. The source, Java/OS identity, processor count, actual
selection, outputs, phase costs and all seven rounds remain in each raw report.

Next measurement targets are first-use preparation/validation cost, the
portfolio's guard/dispatch overhead, residual entry allocation, and the T0
fallback cliff. Broader application workloads and longer independent warmup
cohorts are still needed before making a publication-level performance claim.
