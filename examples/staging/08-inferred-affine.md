# Functional accumulation with inferred private mutation

[`08-inferred-affine.klr`](08-inferred-affine.klr) generates an ordinary
functional two-counter loop. The compiler discovers its private accumulator,
converts it to owned operations, checks the derivation and emits a private
primitive array. The source contains no ownership annotations, and its persistent
seed and earlier results remain valid across calls.

The persistent controller counts layout observations and carries a preparation
budget between batches. Preparation runs in an authority fork; installation
follows fork exit and uses the existing guarded cache. Unsupported programs and
failed entry guards retain functional execution. The profile requests work; it
does not prove ownership or profitability.

Follow the [REPL instructions](../../experiments/adaptive_affine/README.md) to
load the example, run the tests and reproduce the diagnostics. The
[correctness ledger](../../doc/engineering/correctness.md) gives the exact accepted fragment,
proof boundaries, comparisons with Perceus/FIP/Futhark/Rust, and measured costs.

The original array version removed the allocation slope but used a reflective
setter. Independent review replaced it with typed `aset`; the new warmed
diagnostic beats the functional/transient baselines at 4,096 iterations.
See the [review](../../doc/engineering/performance.md) for separate results
and the remaining entry overhead. The companion outcome
predictor shows when parallel speculation can save latency while spending more
CPU, and when training and mispredictions make it a loss.
