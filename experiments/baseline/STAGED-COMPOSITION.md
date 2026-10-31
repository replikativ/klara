# Re-analyzing a checked residual

2026-10-30. This REPL probe tests the next composition boundary without changing
the production preparation policy or adding a new executable IR.

```clojure
(fn [n]
  (let [square (fn [x] (* x x))
        score (fn [x] (+ (square x) 1))]
    (loop [i 0 total 0]
      (if (< i n)
        (recur (inc i) (+ total (score i)))
        total))))
```

Initially `square` is captured by `score`, so the conservative use analysis
cannot eliminate it. One checked round inlines `score`. A second round analyzes
that residual and can now inline `square`. Both use the same guest analyzer,
host checker and ordered recipe. The first receipt's target identity equals
the second receipt's source identity.

| Stage | Calls inlined in this round | Guarded loop layouts admitted |
|---|---:|---|
| Original | — | None |
| First residual | 1 | None |
| Second residual | 1 | Long or Double |

The last column describes conditional layout variants, not an unconditional
claim about all calls. Runtime class guards are still required. This layout
analysis does not propagate the outer constant initializers through the entry
locals, so it admits both variants; actual Long initial values select Long.

The prototype fact record contains an exact named-IR source identity, a domain
version, source-local loop paths, candidate kinds and an explicit entry-guard
requirement. Passing the first residual's facts to the second residual rejects
with `:stale-analysis`, even if some facts happen to remain true. Forging kinds
under the right identity rejects with `:invalid-analysis`: matching identities
alone do not establish facts. Validation currently recomputes the analysis.

The final residual is converted back to Core through the existing indexed
adapter and compiled by the ordinary baseline. Eight inputs include integral,
fractional and invalid bounds. Their values, result classes and failures match
the original interpreted function. The native residual records a hit with no
fallback or deoptimization. Its Core entry identity differs from the original;
this experiment does not silently replace the original function's cache entry.

The recorded run spends 13,370 counted work units, one emission and 696 counted
form bytes, including analysis, rechecking and residual preparation. These are
warm-session counters, not CPU timings, heap/class sizes or complete accounting.
The [raw report](staged-composition-results/repl-0.edn) retains receipts, facts,
observations and source fingerprints.

This is evidence for a bounded production driver that re-analyzes successive
checked residuals. It is not yet that driver, a general fact cache, a rule for
transporting facts across rewrites, or a composition theorem. The next proof
work must establish each recipe's semantic relation and the preservation or
invalidation of its facts. The prototype layout records also do not replace
effect, world-assumption or ownership facts.

In the existing host REPL:

```clojure
(require '[baseline.staged-composition :as composition])
(composition/run-study! "repl-new")
(require 'baseline.staged-composition-test)
(clojure.test/run-tests 'baseline.staged-composition-test)
;; 2 tests, 11 assertions
```

These focused tests live under `experiments`, separate from the standalone core
suite. New reports go under `target/staged-composition/`.
