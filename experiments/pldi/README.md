# JVM evaluation suite (historical cohort)

From the repository root, one command runs tests, spec-diff, the seeded
compiler differential corpus, javac, and ten JVMs **per configuration**:

```
python3 experiments/pldi/run.py
```

Requires the repository's Clojure/JDK dependencies, sibling `ansatz` and
`wandler` checkouts, Python 3, javac and Linux `/proc`/sysfs. No Python
packages are needed. The default output directory has a UTC timestamp; archived evidence is in
`experiments/pldi/results/`. Existing output directories are refused. Use
`--out experiments/pldi/results-new --runs 30` for a fresh larger run.
Javac (128 MB), tests/spec (2 GB), generation/benchmarks (512 MB) and summary
(256 MB) run sequentially; the driver waits for each child, terminates it
on interruption, and removes temporary Java classes. CLI dependency
preparation may also start a JVM, only before the corresponding child.
No daemon or benchmark JVM is retained. Three additional validation JVMs
run sequentially after timing. Analysis script hashes are separately
recorded in `analysis-manifest.json`; the measured worker sources are
frozen by the original source manifest.

`manifest.json` records revision, source hashes, machine, CPU governor,
flags, protocol, configuration order and elapsed wall times. Each
`run-NN-MODE.edn` contains machine/JVM metadata, raw batches, counters,
compile costs, forced checkpoints, observations and event series. CSV
files contain process summaries, with full raw samples in EDN. `summary.*`
and `ratios.*` report process medians and 95% percentile bootstrap CIs
(10,000 resamples, fixed seed); ratios resample paired repetition blocks.
`events-summary.*` resamples complete process event series for p50/95/99.
Latency-only and compilation rows have unmeasured allocation (`n/a` in
tables; raw zero placeholders are not measurements). ThreadMXBean allocation
covers the measurement thread, including entry,
result and driver allocations. Bytes/update divides whole-call allocation
by iteration count; zero-iteration setup is reported separately.

Regenerate tables without rerunning measurements:

```
python3 experiments/pldi/render.py experiments/pldi/results
```

Import `rq1.tex`–`rq5.tex` into the paper with booktabs available. `rq1.tex`
compares the 2,000-iteration kernels and SMC in a compact matrix, in
microseconds per call; `rq1-all-estimates.tex` retains both sizes, allocation
and compilation rows. `tables.md` provides the same estimates for review.

## Workloads and semantic boundaries

RQ1 reuses all seven `experiments/compiler/bench.clj` kernels, at 200 and
2,000 iterations. Each configuration runs in its own JVM. Kernels use
100 T0 warmups or 10,000 optimized/host warmups, then seven batches of five
T0 calls or 500 other calls. This asymmetry makes the T0 cost affordable;
no claim of equal JIT maturity follows. The process is the independent
unit. Java uses the existing primitive algorithm baselines; source-shaped
Java equality is checked in the compiler's original harness.

SMC uses 32 particles, 12 observations, 16 sensor-calibration recurrence
steps per particle/observation, five warmups and seven measured whole runs.
Klara's `choose`/`observe` handlers capture actual T0 continuations;
systematic resampling resumes selected parents with split keys, including
multiple resumptions. The emission kernel is compiled; scheduling,
handlers, model loop and resampling are interpreted. This is a **hybrid
compiled workload**, not general compiled effect handling. The 384 emission
calls do 6,144 numeric microsteps; compiled coverage is reported by these
static work counts, not an invented percentage of execution time. Cache
hit counters exclude direct-slot hits. The standard numeric kernel's
Double loop initially deopts three times, then feedback selects generic
emitted arithmetic. Java and independent Clojure state-machine baselines
have explicit particle state and identical keys, draws and systematic
resampling; they do not supply a general continuation runtime. They check
against Klara's deterministic count and normalizer before timing. Weights
are floating point and zero total mass/mixed completion are explicit errors.

RQ2 runs the same SMC with an owned calibration cell, dynamic T0 checking
versus the existing validated affine erasure. It also compares a licensed
owned vector increment loop, at 0, 1,000 and 10,000 updates. The erasure
comparison includes compilation/runtime representation and interpreter
costs, so it cannot isolate a single check's nanosecond cost. No unchecked
authority variant is installed in production. Unsupported captures,
stale authorities, loans, freeze and forks are covered by the full tests.

RQ3 installs actual reverse dependencies (10, 1,000, 100,000). Publication
updates a prebuilt entry through the real world CAS protocol, without
source parsing/compilation. First-correct latency starts after a source
redefinition returns and includes taking a new fiber and evaluating `g`.
Total and source-publication event times are retained separately. Old
pinned fibers are checked after every new result; concurrent writer/reader
R4 behavior is exercised in the existing full suite. Clojure's ordinary
Var redefinition has direct linking off; its global semantics do not
provide pinned old worlds. No artificial Clojure snapshot is timed.

RQ4's experiment-only emitter injection forces each emitted source
checkpoint: let-spine addition and loop head. The inventory also exercises
virtual vectors, aliases, closures, letrec and live evidence. Fresh caches
ensure feedback cannot hide exits, and values/errors, traces and normalized
stores must equal T0. Existing S7 tests cover hand-authored continuation
frames/handler identities, caller forks, consumed resources and refused
barriers; these are finite tests, not arbitrary checkpoint support.
Mixed inputs use 0/0.1/1/10% non-Long values; ordinary feedback limits exits
to three per site. Recovery timing includes entry/failed guard, exception
transfer and T0 materialization, but excludes cache creation/install.
The deliberately broken replay fallback in `naive-counterexample` repeats
a Counted effect inside a caller fork while returning the same value; it
lives only here. `checkpoint-inventory.edn` additionally records actual
exits from the S7/S9/S11/S12 format tests and explicit let/if frame
injections. Both resume modes, all four frame tags and all seven slot
descriptors must be observed. `smc-validation.edn` compares sixteen fresh
seeds against T0 and an independent exact forward calculation, and tests
false/nil completion, zero mass and mixed completion.
`authority-dispatch.edn` separately counts actual store dispatches with
and without erasure; this instrumentation never enters timing.

RQ5 independently generates 1,000 accepted, 250 HOF and 250 rejected
programs with recorded per-program seeds, six inputs for accepted/HOF and
three for rejected. Accepted/HOF cases also compare after cache deletion.
Distinct syntax counts avoid pretending duplicates are independent programs.
The 69-case spec corpus separately records and classifies its four known
differences. An unexpected disagreement fails the command. Existing suite
generators remain additional regression coverage, not pooled independent
trials. Neither finite differential testing nor tested certificates are
compiler soundness proofs.

The protocol uses ten processes per configuration and a bounded input grid.
Shared-machine noise, short SMC warmup,
fixed small deterministic model, primitive Java algorithms, interpreted
handlers, no peak/retained heap attribution, no affinity/core isolation,
no asymptotic statistical proof and no general compiled capture remain
limitations. Preserve negative results and confidence intervals. Consult
`doc/engineering/performance.md` before generalizing these measurements.
