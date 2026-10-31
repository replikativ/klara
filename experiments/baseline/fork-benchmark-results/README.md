# Fork profitability diagnostic

`repl-final.edn` is the final source cohort for this consolidation. `repl-0.edn`
preserves an earlier run before restricting explicitly funded requests to the
metered baseline backend. Both contain all sample values/times and source
hashes; neither is a multi-process performance evaluation.

See [the implementation account](../../../doc/engineering/preparation-strategies.md#measuring-a-candidate-in-a-fork)
for admission, funding and shared-JVM caveats. Reproduce with:

```sh
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.fork-benchmark fresh
```

This experiment does not use SCI. It writes `target/fork-benchmark/fresh.edn` and
does not promote a candidate into an application cache. Negative tests run as
part of `clojure -M:verify` and do not assert elapsed times.
