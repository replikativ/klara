# Current generic execution comparison

For the newer comparison including compiled Klara, preparation costs and
structural loop lowering, see [execution and investment](INVESTMENT.md).
This document retains its original interpreter-only cohort.

This cohort compares the current default fused T0 driver, two experimental
private execution kernels, published SCI 0.15.59 and compiled host Clojure.
It does **not** measure the local forkable SCI branch. Klara compiler entry
hooks are disabled. The private kernels run through their common entry and
return controller; neither is integrated as the production fallback runtime.

## Results

Three sequential fresh JVMs, Intel Core Ultra 7 258V, Linux x86_64,
JDK `25.0.1+8-LTS-jvmci-b01`, Clojure 1.12.4, 1 GiB heap, JVMCI enabled.
The table gives ranges of process medians, milliseconds per invocation at
`n = 10000`. Preparation and source expansion are excluded.

| Workload | Clojure | SCI | Default T0 | Private nodes | Activation program |
|---|---:|---:|---:|---:|---:|
| Integer summation | 0.00314–0.00325 | 0.121–0.124 | 9.24–9.57 | 2.00–2.16 | 1.53–1.64 |
| Local closure calls | 0.00271–0.00299 | 0.205–0.210 | 14.24–15.31 | 2.75–3.04 | 2.21–2.47 |
| Persistent vector updates | 0.366–0.375 | 0.538–0.562 | 23.59–30.61 | 4.70–5.11 | 3.53–3.95 |
| Host map/reduce, guest callback | 0.0831–0.0851 | 0.137–0.138 | 4.37–4.93 | Unsupported | Unsupported |

The pure private kernels have narrower language coverage. Unsupported cases
are recorded explicitly, without falling back to T0. These are small diagnostic
programs, not broad language benchmarks or guarantees of peak throughput.

For integer summation, allocation per call is approximately 33.04 MB for T0,
0.483 MB for nodes, 0.481 MB for activation programs and 0.477 MB for SCI
(decimal units). Private storage removes substantial allocation, yet nodes
remain about 16–18 times slower than SCI and activation programs about 12–14
times slower. Allocation volume alone cannot explain the remaining gap;
equal bytes also do not imply equal allocation sites, retained heap or GC cost.

The [runtime alternatives review](../interpreter/ALTERNATIVES.md) identifies
generic tail-call handling versus specialized self-tail transfers as one
concrete hypothesis. Repeated dispatch, guard work and primitive lookup also
need isolation before attributing costs. A cheap generic emitted body should
be compared with nodes and the existing checked typed emitter before adding
another interpreter representation. No causal profile or such emitted-body
comparison is claimed here.

## Method and reproduction

Each engine receives 200 warmup calls per size, with engine order rotated.
Nine measured samples contain five invocations each, also in rotating order.
Results are checked against the host result. Inputs include `n = 1000` and
`n = 10000`. ThreadMXBean measures current-thread allocation, including harness
overhead. There is no CPU pinning, retained-heap measurement or guarantee that
every engine has reached its best compilation tier.

```sh
clojure -J-Xmx1g -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"] :deps {org.babashka/sci {:mvn/version "0.15.59"}}}' -M -m baseline.current-tiers 0
clojure -J-Xmx1g -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"] :deps {org.babashka/sci {:mvn/version "0.15.59"}}}' -M -m baseline.current-tiers 1
clojure -J-Xmx1g -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"] :deps {org.babashka/sci {:mvn/version "0.15.59"}}}' -M -m baseline.current-tiers 2
clojure -M experiments/baseline/current_tiers_summary.clj
```

New reports go under `target/baseline/`. The recorded
[summary](current-results/current-tiers-summary.edn),
[tabular summary](current-results/current-tiers-summary.tsv) and raw reports
([0](current-results/current-tiers-0.edn),
[1](current-results/current-tiers-1.edn),
[2](current-results/current-tiers-2.edn)) retain samples, source hashes,
VM arguments, exact results and rejected workload details. The summarizer
checks matching source/runtime cohorts. Historical short-warmup results in
`results/` remain separate and should not be combined with this cohort to
derive speedups.
