# Bounded investment over checked preparation

Implemented 2026-10-30. [`compile.investment`](../../src/klara/compile/investment.clj)
adds an explicit checkpoint over the existing funded preparation, prevalidation
and publication APIs. It does not add a compiler backend or a profiler that runs
an optimizer on every function call. See the
[finite-trace study](../../experiments/baseline/investment-policy-results/README.md)
for measured wins, losses and workload shifts.

## One attempt and a world-defined policy

`investment/bootstrap!` explicitly installs the ordinary Klara function
`klara.compiler/investment`, preserving existing edits. The host entry point is:

```clojure
(investment/attempt! cache reference-root 'kernel arguments job
  {:policy-root compiler-root
   :policy 'klara.compiler/investment
   :remaining-calls 1024
   :allowance-ns 200000000
   :preparation-estimate-ns 30000000
   :preparation-options {:strategy 'my-checked-strategy}})
```

This is a hosted controller API. The policy itself runs as bounded, pure guest
code in its pinned world; it receives inert estimates/observations and returns
exactly `{:action action}`. It cannot supply a checker or native implementation.
The existing `code`/`esc` mechanisms can generate such a policy, but this slice
uses an ordinary function; the host still computes forecast arithmetic and
orchestrates jobs and clocks. Source transformation remains with the existing
checked local-call/private adapters.

| Phase | Permitted progress | Meaning |
|---|---|---|
| Unseen | Probe | Admit source/input replay, then measure current full calls |
| Reference measured | Prepare | Use forecast future savings to sponsor one existing preparation recipe |
| Prepared | Probe | Compare current execution with the proposed portfolio on the same inert input |
| Compared | Install | Publish through existing validation if measured prospective savings justify publication |
| Any phase | Stop | Retain all prior expenditure; leave operational candidates unchanged |

The default pre-preparation decision requires predicted future gross savings to
exceed a safety factor times estimated preparation/validation, comparison and
publication costs. Its candidate cost is a declared fraction of observed current
cost. These are uncertain forecasts, not inferred runtime types, correctness
facts or calibrated confidence bounds. After comparison, the publication decision
uses incremental future savings: preparation is sunk. Complete trace accounting
still includes that preparation, including an ultimately unprofitable attempt.

A caller may select a different bounded policy and existing preparation options.
The host enforces phase order, at most one preparation and two probe phases per
attempt, and the original admission/publication boundaries. A policy can waste
its authorized work; no profitability theorem is claimed.

## Isolation and evidence

Before replay, `service/invoke` validates the source/dependency closure, exact
inert arguments and successful fuel-bounded reference evaluation. Arbitrary host
calls, effects, opaque input objects and escaping non-data results decline.
Existing replay caches conservatively require baseline-compiler candidates;
a pure original does not sandbox an arbitrary handwritten host implementation.
Trusted compiler/host behavior remains part of this boundary.

Reference and proposed portfolios get fresh cache hooks, counters and feedback.
They share immutable publication data and existing validity memos. The proposed
cache starts with the current portfolio, so priority and fallback competition
are measured too. A new candidate that fails its current guard or is shadowed
by another candidate declines before publication. An observed portfolio change
before publication also rejects the attempt; the check is not a transaction
isolating concurrent application activity.

Preparation uses an isolated world/authority context, then prevalidates and
installs only into the probe cache. Reference and candidate runs use fresh replay
worlds/stores with the same pinned reference root. Root identity is checked after
execution. Observed values must match the admitted reference, including literal
numeric representations. Matching sampled values is a regression check;
semantic authority still comes from the existing compiler checker and guards.

Forks share host JIT, GC, clocks and compiler infrastructure. This is neither a
sandbox for arbitrary mutable host memory nor a complete persistent process
snapshot. Probe samples alternate reference/candidate order, but short probes
remain sensitive to warmup, noise and drift. Installed code retains its ordinary
world/layout guards. There is no automatic retirement of a slower candidate.

## Budgets and accounting

A shared `Funding` charges validation/stepping, preparation work, emitted form
bytes and emission attempts. Replay reserves reference-transition-equivalent work
for each native/reference sample; that is sponsorship, not measured native
instruction or CPU accounting. Failure or discard does not roll these counters
back. Samples and service data have fixed bounds.

`:allowance-ns` is a measured phase-spend limit checked before starting another
phase. A host compilation, native call or GC can overrun it; there is no wall-clock
preemption. Events retain phase durations on failures too. `:spent-ns` sums those
phases; surrounding controller bookkeeping is included by the study's external
attempt timer and whole-trace timer. Runtime allocation limits from the
[allocation agenda](../objectives.md#bounded-allocation-and-reusable-storage) are not implemented by this allowance.

The finite horizon describes future application calls after the extra probe calls;
probes do not consume the input stream. Callers choose checkpoint frequency and
forecast the horizon. The study counts the cost of its checkpoint and probes,
and tests a time-ordered layout shift; it does not implement general drift
inference, a trained predictor or a global investment scheduler.

## Checks and next boundary

[`investment-test`](../../test/klara/compile/investment_test.clj) checks deterministic
policy decisions, normal publication, phase/action rejection, failed/exhausted
charges, input guard misses, zero time allowance, accounted reference exceptions, effect rejection before source
execution, host-cache replay rejection and parent-world preservation. No test
asserts an elapsed-time speedup.

The [campaign review](performance.md) now reaches its consolidation
checkpoint after this bounded implementation and the
[actual syntax correspondence slice](actual-inline-correspondence.md).
Future improvements should follow measured total costs: cheap prefilters or
longer amortization windows may beat more elaborate policy. Learned estimates,
allocation-capacity specialization and broader replay admission remain separate
extensions through these boundaries.

## Explicit scheduling

Use one existing preparation job for fixed and threshold scheduling:

```clojure
(require '[klara.compile.prepare :as prep])
(def job (prep/job {:session-limits {:work 131072 :emissions 16 :bytes 1048576}}))
(def schedule (prep/sponsor job {:mode :threshold :threshold 32}))
;; root is an immutable snapshot, cache the application's stage cache.
;; Report calls/work events explicitly at a chosen checkpoint:
(prep/checkpoint! schedule root {:name 'app/kernel :file "app.cljc"} cache 1)
;; => {:status :waiting :events 1 :threshold 32}
```

`:interpret` skips; `:before-use` prepares at the first checkpoint (zero events
is allowed); `:threshold` accumulates caller-declared nonnegative events. At the
threshold the same `prepare!` performs bounded baseline preparation, validation
and publication with the job's recipe/options and counter ancestry. Events are
not units of preparation work or a correctness premise. The controller records
at most 1,024 request identities, saturates counts and attempts once per request
and exact root. Errors/declines remain attempted; no automatic retry refunds
work. A new root resets that request's counter. A fresh controller can explicitly
retry but shares the job's remaining allowance. Concurrent checkpoints serialize
per controller. Do not use this optional host checkpoint on every hot iteration.

The loader remains a direct before-use caller. Measured `attempt!` remains
opt-in because it needs inert replay inputs, policy and cost forecasts. No
ordinary-call optimizer, global profiler or autonomous retirement is implied.
The four-policy historical cohort used an experimental threshold at call 8;
it predates this API and is retained unchanged. These scheduling choices make
AOT a choice of when to run preparation, not a different compiler.
