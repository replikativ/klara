# Performance evidence and costs

The repository retains measured wins, losing cases, raw samples and original
source/runtime identities. These historical measurements are not fresh results
for the current source tree. A successful correctness check does not establish
profitability or performance parity with Java.

## Measurement entry points

| Family | Evidence and reproduction | Scope |
|---|---|---|
| Generic interpreter baseline | [T0/SCI/Clojure diagnostic](../../experiments/baseline/README.md) | Four shared workloads, three fresh JVMs, allocation and separate JFR samples; compiler hooks disabled |
| Bounded investment and refreshed campaign | [Finite-trace study](../../experiments/baseline/investment-policy-results/README.md) | Four policies, three JVMs, full trace CPU/allocation/costs, losing short/layout-shift cases and a new five-family cohort |
| Shared entry work | [Entry study](../../experiments/baseline/entry-results/README.md) | Matched ordinary traversal controls, live resolution counters, allocation and current-only direct/evidence observations |
| Mandatory compiled baseline | [Staged baseline diagnostic](../../experiments/interpreter/STAGED-BASELINE.md) | Three fresh GraalVM 25 JVMs; separate namespace/preparation/install costs, full calls, actual guest transfer receipts and declines; tiny-call regression retained |
| Compilation investment | [Matched engines and costs](../../experiments/baseline/INVESTMENT.md) | SCI/Clojure/T0/private/compiled controls; entry and structural ablations, lazy loading, payback estimates and checked direct-loop promotion |
| Wider program coverage | [Persistent data and calls](../../experiments/baseline/COVERAGE.md) | Histograms, materialized records, tree worklists, constructor control, local-call declines and mutual-call capability |
| Literal and local-call refinements | [Warm REPL diagnostic](../../experiments/baseline/REFINEMENTS.md) | Map representation and exact array stores; loop/escape/layout analysis composition; unchanged T0 fallback |
| Checked guest local analysis | [Staged planner diagnostic](../../experiments/baseline/STAGED-LOCAL.md) | Guest use analysis, checked inline recipe, native execution and separately metered preparation; one warm process |
| Composed ownership families | [Allocation and admission study](../../experiments/baseline/OWNERSHIP-FAMILY.md) | Captured updates, branching recurrences, bounded histogram, size-dependent allocation and evidence-entry ablation; restricted observations, one warm process |
| T0 driver optimization | [Reference/fused driver experiment](../../experiments/interpreter/README.md) | Paired ordinary/control-boundary workloads; explicit reference driver retained |
| Private mutable CEK | [Memory representation probe](../../experiments/interpreter/MEMORY.md) | Closed pure fragment, compact nodes, reusable mutable working state and explicit snapshots; experimental, not installed as T0 |
| Activation programs | [Representation comparison](../../experiments/interpreter/ACTIVATION.md) | Shared controller and admission; separate preparation, matched snapshots and recovery; small-call regressions prevent general promotion |
| Checked counted-loop emission | [Same-source comparison](../../experiments/interpreter/COUNTED-LOOP.md) | Scalar step proofs, generic/primitive bodies, full entry costs and backedge recovery; proof/preparation costs remain substantial |
| JVM interpretation versus C2 | [Primitive Java control](../../experiments/interpreter/jvm_modes/README.md) | Explicit `-Xint` and verified C2 kernels; wrapping/checked arithmetic, not a paired SCI/Klara benchmark |
| Handler costs | [Handler experiment](../../experiments/handlers/README.md) | Hosted control/effect mechanisms; not a whole-language benchmark |
| JVM evaluation suite | [Evaluation experiment](../../experiments/pldi/README.md) | Historical source cohorts, multiple processes and recorded baselines; its directory name is a retained experiment identifier |
| Typed scalar JVM probe | [Typed JIT](../../experiments/history/typed_jit/README.md) | Guarded primitive bodies and host/backend integration |
| Staged scalar lifecycle | [Staged regions](../../experiments/history/staged_regions/README.md) | Generation, preparation, installation and guarded invocation |
| Private accumulation | [Adaptive affine experiments](../../experiments/adaptive_affine/README.md) | Shared lowering, allocation and original versus corrected residuals |
| Composed numeric/private loop | [Benchmark summary](../../experiments/consolidation/benchmark-summary.md) | One-family independent-process pilot; body, guards, full calls and preparation |
| Producer/consumer admission | [Admission summary](../../experiments/consolidation/admission-summary.md) | Input scan, reusable evidence and fixed-worker entry; materialized producer output |

The [speculative pipelining teaching example](../../examples/staging/16-learned-speculation.md)
has correctness tests but no speedup claim. Its original host predictor benchmark
records training, prediction, validation, fallback and wasted CPU separately.
These are different programs and their measurements must not be conflated.

## Where overhead comes from

[Private preparation attribution](../../experiments/baseline/preparation-results/README.md)
separates first backend loading from warm preparation and replaces duplicated
analysis with a candidate-local artifact check. Three JVMs compare single and
repeated production with the same checker; erasure/registry validation remains
active. The study records why a broad erasure-verdict cache was deferred.

The [three-process wider campaign](../../experiments/baseline/campaign-results/README.md)
adds helper loops, persistent maps, tree worklists, private accumulators and
closure declines. It records preparation, validation, publication, warm/full
calls, current-thread CPU and allocation, with finite-horizon estimates.
Private lowering reduced per-call work in its admitted family, but its larger
preparation cost lost to baseline over the reported 1000-call horizon. Portfolio
dispatch, first-use compiler/validation cost and T0 fallback remain measured
targets. These short cohorts do not establish peak C2 performance.

The generic T0 driver now fuses immediate operands and common transitions,
and calls anchored arithmetic functions at fixed arity for exact Long/Double
operands. The [paired driver experiment](../../experiments/interpreter/README.md)
records lower allocation and faster process medians on eight bounded workloads,
including control boundaries. Explicit stepping and the original driver remain
available. Suspended frames remain persistent; this change does not implement
managed atoms, a new heap model or a mutable continuation stack. It also does
not remove argument/environment allocation or establish general interpreter
competitiveness.

The executing JVM instruction alone does not explain a Klara call's cost.
Selector layers, argument vectors/`apply`, context access, guard checking,
generic return layouts and boxed arithmetic can all surround it. Measurements
must distinguish per-iteration costs from per-call costs; a loop iteration
can contain several calls. A predictable interface call can be inlined by the
host VM while surrounding adaptation remains expensive.

The implementation includes direct-call paths and explicit context for its
compiler subset. Known higher-order callbacks can be inlined into vector loops
under their supported conditions, preserving relevant lazy chunk boundaries.
Unknown escaping callbacks and unsupported effects fall back. It is not a
general optimization of arbitrary higher-order Clojure programs.

Composed numerical/private loops use primitive arrays and checked arithmetic.
The corrected emitter uses typed setters; the original reflective-setter
measurements remain preserved as an older cohort. Snapshot RHSs are evaluated
before stores. Scalar RHS lets are supported. Output projection, per-invocation
objects, guards and generic fallback can still dominate small workloads.

The bounded-vector guard uses indexed primitive comparisons after an earlier
sequence-based scan showed allocation proportional to length. Full invocation
still includes a linear scan unless matching subject-bound facts discharge it.
An admitted batch can amortize entry work across a fixed worker; it does not
eliminate producer allocation or establish complete stream fusion.

## Losing cases and accounting

The counted-loop probe reaches microsecond execution close to its compiled
Clojure controls after lifting the iteration-budget calculation out of the
loop. Its generic emitted body also benefits from stable host-JIT sites.
That result applies to two closed scalar loops. Per-source symbolic proof
generation costs tens of milliseconds, and cold model construction takes
seconds; those costs are separate from residual execution and must be budgeted
or moved into preparation. No automatic production-tier promotion follows.

Small workloads can lose after compilation, installation and admission costs.
Private storage can reduce allocation without making full invocation faster.
High prediction accuracy can still lose after scheduling, validation, training,
fallback and duplicated work. Large synthetic speculation samples can be close
enough to zero to change sign; the recorded repeats remain visible.

Resource policy must distinguish latency from total CPU, retained memory and
opportunity cost. A spare worker can reduce one request's latency while using
more resources; the same choice can hurt throughput on a saturated machine.
The current guest planner uses supplied estimates, and the teaching pipeline
always attempts speculation. Comprehensive metering and calibrated investment
policies remain objectives.

## Reporting discipline

Record source/dependency identities, JDK/VM settings, hardware, input sizes,
seeds, warmup, process count and raw samples. Report full guarded invocation,
preparation and amortization alongside residual body costs. Keep output
materialization, scans and losing inputs visible. Do not subtract independent
medians to fabricate additive component timings.

Use `target/` for new reports instead of overwriting historical data. Pilot
workload families and one-machine measurements do not establish broad language
performance. JVM machine-code generation remains part of the backend; dedicated
non-JVM targets and a complete low-level compiler are not implemented.
