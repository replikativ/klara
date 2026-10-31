# T0, SCI and Clojure shared-fragment diagnostic

The [compilation investment study](INVESTMENT.md) adds matched compiled paths,
entry boundaries, preparation costs and subsequent direct-loop lowering.
The [wider coverage study](COVERAGE.md) adds map/record/tree programs and makes
closure-call and native mutual-recursion coverage gaps explicit.

For the newer, more thoroughly warmed comparison of the current driver and
private kernels, see [current execution results](CURRENT.md). The recorded
table below remains a historical diagnostic.

This measures Klara's generic T0 interpreter against SCI and host Clojure on
the same four small source forms. Klara compiler entry hooks are disabled.
SCI 0.15.59 is an optional benchmark dependency; it is not the interpreter
implementation of Klara. These results do not compare compiled peak speeds.
The recorded cohort predates the fused T0 driver. Re-running this command
measures the current default driver; the separate
[driver comparison](../interpreter/README.md) measures original and fused
execution against the same current sources.

## Reproduce

Run fresh JVMs sequentially on an otherwise idle machine:

```sh
clojure -M:baseline 0
clojure -M:baseline 1
clojure -M:baseline 2
clojure -M experiments/baseline/summarize.clj
```

Reports go to `target/baseline/process-N.edn`; the summary rejects mixed source
or runtime cohorts. Each report retains all samples, source hashes, JVM flags,
OS information and exact results. Preparation is measured separately and
excludes namespace/dependency loading. Each engine receives 30 warmup calls,
then nine samples of ten calls, in fixed engine/workload order. Allocation is
measured on the current thread with `ThreadMXBean` and includes measurement
overhead. There is no claim that 30 calls reaches steady state. Tiering,
frequency changes and ordering can materially affect these short runs.

## Recorded diagnostic

The [raw reports](results/process-0.edn) and [summary](results/summary.edn)
record three sequential JVMs on an Intel Core Ultra 7 258V, Linux x86_64,
JDK `25.0.1+8-LTS-jvmci-b01`, Clojure 1.12.4, with a 1 GiB heap and JVMCI
enabled. The source hashes identify the measured working tree; these are not
measurements of the preceding Git revision. Values below are ranges of
per-process medians for `n = 1000`, in milliseconds per call:

| Workload | Clojure | SCI | Klara T0 | T0 allocated bytes/call |
|---|---:|---:|---:|---:|
| Integer summation loop | 0.023–0.024 | 0.029–0.030 | 2.66–2.76 | 9.14–9.17 MB |
| Local closure call in loop | 0.055–0.058 | 0.191–0.301 | 4.03–4.23 | 13.97–14.00 MB |
| Persistent two-slot vector update | 0.096–0.125 | 0.082–0.085 | 5.32–5.67 | 18.73–18.79 MB |
| Host map/reduce with guest callback | 0.014–0.043 | 0.023–0.055 | 1.09–1.38 | 4.22–4.24 MB |

MB uses decimal units. Raw reports also include `n = 100`. Small-input and
cross-process variation make precise speedup ratios inappropriate. There is a
clear diagnostic signal of high T0 allocation and dispatch cost; this needs
attention for fallback execution and guest compiler orchestration. The four
programs do not establish broad language performance or locate every cause.

## Allocation investigation

A separate JFR run provides sampling evidence without mixing instrumentation
into the table above:

```sh
clojure -J-XX:StartFlightRecording=filename=target/baseline/allocation.jfr,settings=profile,dumponexit=true -M:baseline allocation
jfr print --json --events jdk.ObjectAllocationSample target/baseline/allocation.jfr > target/baseline/allocation.json
python3 experiments/baseline/allocation_summary.py target/baseline/allocation.json
```

In the recorded [sample summary](results/allocation-summary.json), persistent
vectors and object arrays dominate the sample weight whose captured stacks
include a Klara evaluator frame. The most frequent attributed evaluator
locations by weight are `eval-list` and `step-eval`, followed by `step-ret`
and `host-apply`. This supports investigating machine-state, argument and
continuation construction before blaming interface invocation alone.

JFR weights are estimates, not exact object counts or a complete allocation
breakdown. Limited stack depth misses evaluator callers, and the recording
includes startup, expansion, preparation and all engines. It does not isolate
per-workload GC cost, retained memory or the cost of Klara's semantic features.
The binary recording remains a generated file under `target/`.

The [entry study](entry-results/README.md) compares ordinary guard traversal
with publication-time binding plans, including live/dynamic-root regression
cases, allocation and current-only direct/evidence observations.
