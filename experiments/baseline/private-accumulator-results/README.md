# Enclosed accumulator diagnostic

See [the implementation account](../../../doc/engineering/private-accumulator.md)
for the guest example, accepted boundary and tested semantic bridges.

`before/` preserves the baseline/controller source before adding the terminal
endpoint. Raw reports contain source hashes, input, every sample, preparation
and validation costs, and candidate cache statistics:

| Report | Iterations | Warm-process median: T0 / baseline / private |
|---|---:|---:|
| `repl-0.edn` | 1,000 | 3.47 ms / 107 µs / 84.8 µs |
| `repl-10000.edn` | 10,000 | 36.9 ms / 249 µs / 153 µs |
| `repl-final.edn` | 10,000 | 36.2 ms / 520 µs / 104 µs |

These are successive cohorts in one long-lived REPL, not independent processes.
Their variation is a reason not to infer a stable speedup ratio. Each uses
twenty warmup calls per engine and nine rotating-order timing rounds. The
baseline also receives the checked local-call inlining; the private variant
adds the enclosed owned endpoint. Both are installed calls including guards.
The final vector freeze still allocates. No timing result is a test assertion.
Baseline direct-call caching does not increment the same hit counter on every
call, so hit counts are not comparable invocation counts across engines.

Reproduce a fresh cohort with:

```sh
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.private-accumulator fresh
```

The output goes to `target/private-accumulator/fresh.edn`. This is a diagnostic
fixture, not an autonomous profiler or general fork-replay API. Inputs and
source are fixed and pure. No application-world state or source is published.
