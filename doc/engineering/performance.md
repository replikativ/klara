# Performance evidence and costs

The repository retains measured wins, losing cases, raw samples and original
source/runtime identities. These historical measurements are not fresh results
for the current source tree. A successful correctness check does not establish
profitability or performance parity with Java.

## Measurement entry points

| Family | Evidence and reproduction | Scope |
|---|---|---|
| Handler costs | [Handler experiment](../../experiments/handlers/README.md) | Hosted control/effect mechanisms; not a whole-language benchmark |
| JVM evaluation suite | [Evaluation experiment](../../experiments/pldi/README.md) | Historical source cohorts, multiple processes and recorded baselines; its directory name is a retained experiment identifier |
| Typed scalar JVM probe | [Typed JIT](../../experiments/typed_jit/README.md) | Guarded primitive bodies and host/backend integration |
| Staged scalar lifecycle | [Staged regions](../../experiments/staged_regions/README.md) | Generation, preparation, installation and guarded invocation |
| Private accumulation | [Adaptive affine experiments](../../experiments/adaptive_affine/README.md) | Shared lowering, allocation and original versus corrected residuals |
| Composed numeric/private loop | [Benchmark summary](../../experiments/consolidation/benchmark-summary.md) | One-family independent-process pilot; body, guards, full calls and preparation |
| Producer/consumer admission | [Admission summary](../../experiments/consolidation/admission-summary.md) | Input scan, reusable evidence and fixed-worker entry; materialized producer output |

The [speculative pipelining teaching example](../../examples/staging/16-learned-speculation.md)
has correctness tests but no speedup claim. Its original host predictor benchmark
records training, prediction, validation, fallback and wasted CPU separately.
These are different programs and their measurements must not be conflated.

## Where overhead comes from

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
