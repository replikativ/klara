# Literal construction and local calls

2026-10-30. These changes address two gaps exposed by the
[wider coverage study](COVERAGE.md), using the existing hosted compiler.
They do not change T0's execution representation or add a new backend.
The subsequent [staged guest-analysis slice](STAGED-LOCAL.md) exposes a checked
local-call recipe through the bounded preparation job; this document retains
the earlier hosted-analysis measurement cohort.

## Map syntax

New dynamic map literals expand to a distinct `literal-map` Core opcode.
Its reference implementation uses Clojure's `RT.map` representation selection
and duplicate-key checking. Small maps use array maps and larger maps use hash
maps. Explicit `hash-map` calls and previously stored Core `hash-map` nodes keep
their original meaning. Fully constant map literals retain their quoted value.
This is a frontend semantic alignment, not permission to change an arbitrary
existing map's observable host class.

The shared JVM lowering evaluates keys and values in order into a private
reference array. It selects `RT.mapUniqueKeys` when uniqueness is established,
otherwise `RT.map`; the empty case retains the singleton empty array map.
The array never escapes independently of the persistent result and is never
mutated after construction. Known duplicate constant keys reject during
expansion; dynamic duplicates fail after evaluation, preserving prior errors.

An initial implementation revealed an important backend trap: Clojure's generic
`aset` can compile to reflective dispatch for an `Object[]` and primitive numeric
value. In this experiment that produced about 248 MB/call and 34–35 ms despite
successful native entry. Selecting the exact reference-array store overload
removed that overhead. Tests enable reflection warnings for this case and
require compiled hits, rather than allowing equality through fallback to pass.

The corrected paired constructor experiment measured 5,000 records:

| Variant | Warm median, µs | Current-thread MB/call |
|---|---:|---:|
| Clojure map literals | 516 | 2.42 |
| Klara baseline map literals | 437 | 2.34 |
| Clojure explicit `hash-map` | 755 | 3.85 |
| Klara baseline explicit `hash-map` | 1,035 | 4.26 |

This is the final constructor run in one existing GraalVM REPL, not independent
process medians or a peak-performance claim. It uses 500 warmups per variant,
nine rotating samples and 20 calls per sample. Warmup and compilation history
can change allocation and code quality. Read the recorded source hashes before
comparing cohorts. The recorded corrected report additionally asserts compiled
hits and zero fallbacks/deoptimizations.

## Local functions in direct loops

The optimizing compiler now composes its existing structural loop validator
with escape analysis. A validated directly entered self-tail function is an
internal control boundary, so merely capturing a local helper there no longer
means the helper escapes. All entry-argument and body uses are inspected;
returning the helper, storing it as a value or capturing it in an arbitrary
nested function still rejects elimination. Existing copying/freshening and
ordered beta reduction perform the inlining.

```clojure
(fn [n]
  (let [score (fn [x] (+ (* x x) 1))]
    (loop [i 0 total 0]
      (if (< i n)
        (recur (inc i) (+ total (score i)))
        total))))
```

The loop layout analysis also distinguishes a comparison's Boolean result
from its operands' layouts. An unknown captured bound does not prevent proving
that `i` and `total` stay longs. The comparison remains generic and can fail;
its evaluation is not moved or removed. An unknown numeric value contributing
to the next accumulator does still prevent the invariant proof. The emitted
fast path retains entry class guards and checked arithmetic. This is a small
abstract interpretation rule, not specialization on one benchmark's syntax.

The [local-call runner](local_calls.clj) records the emitted form, layouts,
preparation, allocation, cache counters and matched results. The mandatory-only
baseline still declines this local closure: it deliberately omits discretionary
escape analysis and partial evaluation. These analyses are currently hosted
Clojure passes; they have not yet been moved into world-managed guest services.

The final warm REPL run at 10,000 iterations recorded:

| Variant | Median, µs | Current-thread bytes/call |
|---|---:|---:|
| Clojure | 4.80 | 26 |
| Klara optimizing | 5.27 | 450 |
| Klara T0 | 19,176 | 61,923,072 |

Compilation took 25.43 ms and validation/installation 1.06 ms in this already
loaded process. Clojure form compilation took 1.05 ms. These are individual
preparation observations, not startup distributions. The runner warms compiled
variants for 2,000 calls and T0 for 20, then takes nine rotating samples of
100 compiled calls or one T0 call. The installed loop has a long layout and
records no fallback or deoptimization. Cache hits count entry resolution;
they are not a count of all invocations after the entry has been cached.

The corrected constructor report is retained under [literal-results](literal-results/);
the final local-call report, including readable emitted host code, is under
[local-call-results](local-call-results/). Older coverage/constructor reports
remain unchanged. These REPL runs supplement the independent-process cohorts;
they do not replace them with a stronger statistical claim.
The constructor cohort predates a comment-only edit to `src/klara/core.clj`;
its exact version is retained as `literal-results/core-before-comment.clj.txt`.
The older `literal-results/before/` sources preserve the pre-literal work and
are not the corrected constructor cohort. The local-call report fingerprints
the current production sources and its runner.
Later compiler changes are preserved separately under
`staged-local-results/before/`; use those versions of `baseline.clj`,
`prepare.clj`, `service.clj` and `staged.clj` to match this cohort's fingerprints.

## Boundaries and reproduction

Lexical freshening does not establish module or phase hygiene; see the explicit
[binding design boundary](../../doc/engineering/bindings-and-modules.md).
The same consolidation also adds [ordered template composition](../../doc/engineering/code-views.md)
for guest Code generators. Neither that API nor these analysis changes is a
new universal correspondence theorem.

In a host REPL with `src` and `experiments` on the classpath:

```clojure
(require '[baseline.local-calls :as calls])
(calls/run-study! "repl-new")
```

The constructor runner also needs the optional SCI dependency used by the older
coverage harness:

```clojure
(require '[baseline.constructors :as constructors])
(constructors/run-study! "repl-new")
```

Both functions preserve the REPL. Fresh process entry points are available via
`-m baseline.local-calls` and `-m baseline.constructors`. New reports go under
`target/local-calls/` and `target/literal/`. Historical reports remain separate.
T0 still has a large fallback cliff. Broader compilation removes dispatch for
admitted programs; it does not reduce the cost of genuinely unsupported code.
