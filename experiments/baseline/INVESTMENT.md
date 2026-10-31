# Execution speed and optimization investment

2026-10-30. These experiments separate emitted code, installed entry, optional
optimization and preparation. They use default Oracle GraalVM 25, not forced
C2, on the local development machine. All runs are sequential; none establishes
language-wide peak performance or a wall-clock compilation bound.

## Matched comparison before structural loop lowering

The [raw cohort](investment-results/) compares published SCI 0.15.59, host
Clojure, T0, the two experimental private interpreters, mandatory compilation
and the existing optimizing compiler. The first four workloads are exactly
those in the [earlier comparison](CURRENT.md). Additional small functions,
vector recurrences and a loop carrying its bound expose input-size and layout
effects. The local forkable SCI branch is not measured.

Every admitted engine checks its results against host Clojure. Unsupported
programs are recorded; they do not silently execute through another engine.
Native admission counters do not count every memoized native call. Allocation
is current-thread allocation, not compiler-thread allocation or retained heap.

Three fresh JVMs run 200 warmup calls per engine/input, then nine samples in
rotating engine order. Each sample has 100 calls for inputs below 100 and five
otherwise. The stage-cache context surrounds each sample, as it normally
surrounds a guest computation. Timings include invocation and selection, but
exclude parsing/preparation. Preparation, validation and installation are
recorded separately. Warmup and workload order affect the VM; these are
diagnostics, not guaranteed steady-state results.

Ranges below are ranges of process medians, in microseconds per invocation:

| Program | Clojure | SCI | T0 | Mandatory baseline | Existing optimizing |
|---|---:|---:|---:|---:|---:|
| Sum, 10,000 iterations | 3.36–4.11 | 110–137 | 9,921–13,144 | 9.69–11.22 | 81.88–109.43 |
| Sum with bound carried, 10,000 | 3.18–3.45 | 126–144 | 9,918–12,238 | 8.55–12.58 | 3.60–4.40 |
| Persistent updates, 10,000 | 307–331 | 568–633 | 24,185–26,033 | 355–383 | 541–580 |
| Vector recurrence, 64 steps | 1.07–2.19 | 2.69–3.23 | 76.97–94.23 | 2.89–3.67 | 4.73–5.47 |

The earlier 14 microsecond recurrence was a different invocation/warmup
cohort; it should not be compared to SCI's 10,000-step sum. Here, SCI and
Klara actually run the same programs. Small vector recurrences are close to
SCI. Large sums and updates favor compiled Klara in this cohort.

Coverage remains important: the captured local-closure workload declines in
both compilers. The host-callback workload compiles only through the existing
optimizing path; the mandatory path deliberately excludes HOF rewriting.
Private interpreters have still different coverage. See raw rejection reasons.

The existing optimizing path is not monotonically faster. It deoptimizes three
times on vector-state programs before feedback settles; the recorded fallback
counter remains zero, so zero fallbacks alone is insufficient evidence of
fully native execution. Mandatory candidates have zero recorded deopts and
fallbacks. On the original numeric sum, the optional compiler retains a loop
check and fails to establish a layout for its captured bound. Carrying the
bound in the loop ABI allows its current invariant analysis to admit a Long
variant. The `:loop-layouts` field is diagnostic; the mandatory compiler does
not consume that analysis.

## Entry boundaries and structural experiment

Separate entry studies give each fast variant 2,000 further warmup calls and
nine batches of 100 calls. They run after the matched rows for that workload,
so the extra warmup does not contaminate its matched rows. They compare an
installed call inside a session, re-entering the cache context per host call,
and the emitted body with admission bypassed. The bypass is diagnostic only,
on the exact immutable input cohort; it is not an alternate safe public entry.

For the 10,000-step sum, the original baseline body reaches 3.37–3.56 µs;
installed session entry is 3.92–4.54 µs and per-call host entry 4.69–5.22 µs.
The tiny function's body is 53–60 ns versus 432–631 ns through session entry
and 1.12–1.21 µs through host entry. These are separately measured variants,
not an additive decomposition obtained by subtracting independent medians.
The changing results also show why warmup must be reported.

The [structural experiment](loop_emission.clj) holds named source and generic
operations fixed while replacing a validated directly entered local recursive
function with ordinary Clojure `loop/recur`. It does not use new input-type
guards, profiling or a proof search. Ordered entry temporaries preserve
application argument order and scope. This uses the shared loop view, rather
than recognizing particular arithmetic programs.

Three additional fresh JVMs, with 3,000 warmup calls and nine batches of 100:

| Sum, 10,000 steps: emitted body | Process-median range µs | Allocated bytes/call |
|---|---:|---:|
| Host Clojure | 3.10–3.85 | 24.64 |
| Generic local function | 4.03–206.85 | 96.64–476,640.64 |
| Direct Clojure loop | 3.30–3.76 | 72.64 |
| Direct loop retaining the speculation check | 9.82–10.01 | 72.64 |

These body tests run without an active feedback cache; their check-bearing
variants are not a controlled reproduction of every cost of the installed
optimizing compiler. Nevertheless, they separate structural lowering from
checking and show substantial host-VM sensitivity of generic local functions.
Vector recurrence bodies show no consistent improvement from this rewrite.

The experiment also checks six source programs against host Clojure and the
old emitter, at eight inputs each: numeric/vector recurrence, simultaneous
swaps, mixed Long/Double/BigInt arithmetic, bad inputs, entry failures and
overflow. Successful outcomes include representation-sensitive result IDs;
failures compare exception classes. This is a finite regression set, not a
universal compiler proof.

`javap` of the direct sum body confirms primitive `long` locals and checked
`Numbers.inc:(J)J` / `Numbers.add:(JJ)J` calls, rather than merely inferring
primitive execution from elapsed time. The external bound still has Object
layout (`Numbers.lt:(JLjava/lang/Object;)Z`). Machine-code generation still
belongs to the host VM. This reaches host Clojure's own representation without
requiring a complete type system or a new bytecode backend.

## Preparation and payback

For already-loaded compiler namespaces, the original sum's first baseline
preparation costs 11.17–14.81 ms, including the first compiled transfer producer.
The later carried-bound preparation costs 2.80–4.84 ms. Five further emissions
of each source in each process show roughly 1.04–2.89 ms for the tiny baseline
and 1.95–3.29 ms for the original sum. These fresh emissions are not executable
cache hits; repeatedly compiling the same unchanged code is avoidable work.
Validation, installation, allocation and counted work remain in the raw reports.
The legacy optimizing compiler's budget usage is empty: it is not metered by
the new mandatory preparation budget merely because the harness passes one.

Paired within each JVM, estimated calls to repay baseline preparation relative
to already-loaded T0 are:

| Program/input | Calls to repay preparation |
|---|---:|
| Sum, 10,000 | 2 |
| Persistent updates, 10,000 | 1 |
| Vector recurrence, 64 | 42–50 |
| Vector recurrence, 8 | 223–287 |
| Tiny addition | 7,851–17,187 |

These are estimates from later measured medians, not observed cumulative
execution trajectories. They exclude shared compiler loading, do not predict
the duration of world validity, and do not imply a calibrated online policy.
Investing in the optimizing compiler after the carried-bound baseline repays
in an estimated 504–1,064 further calls. For the original sum and vector-state
programs it has no measured payback over the baseline because it runs slower.

The [fresh lazy-loader measurements](investment-results/) capture a different
boundary: loading the base runtime takes 1.06–1.19 s; a first ordinary load
22.05–25.37 ms; the first prepared load 324.96–332.48 ms; a second prepared
load 12.02–12.37 ms. Runtime and prepared loads are separate timed operations,
not an additive component estimate. JVM startup before `-main` is excluded.
The first prepared load includes lazy compiler loading and bootstrap. Both
before and after the ordinary load, the preparation namespace is absent.
Do not use the two-call sum estimate to claim a two-call cold-start payback.

Budget probes retain explicit failures: zero work stops with an aggregate
remainder; zero emissions spends admission/form work but emits nothing; one
emission installs one definition and deduplicates its repeated request. A
declined staging definition does not refund its charged work. Counters bound
specified work, not JVM latency, JIT activity, retained classes or GC.

## Promoted direct-loop baseline

The opt-in mandatory baseline now enables the structural lowering. The shared
validator must establish a direct entry and non-escaping self-tail transfers;
other shapes retain the earlier lowering or decline. Entry arguments evaluate
into temporaries before loop bindings. Backedges still consume independently
checked guest-produced transfer plans. No optional numeric analysis, profile
guard, unchecked arithmetic or new semantic Core operation is introduced.
The existing optimizing mode and default loader policy are unchanged.

[After-promotion raw reports](investment-after-results/) use three new fresh
JVMs with the same harness and measurement protocol. They are a different
source cohort from `investment-results` and must not be pooled with it.

For the 10,000-step sum:

| Measurement | Klara baseline µs | Clojure µs | SCI µs |
|---|---:|---:|---:|
| Matched 200-call warmup | 9.66–12.15 | 3.04–3.91 | 121.23–141.04 |
| Additional-warmup session entry | 3.55–4.03 | 2.77–3.01 | 97.20–126.42 |
| Additional-warmup emitted body | 2.72–3.33 | — | — |

The short-warmup installed medians overlap the earlier baseline. There is no
established broad end-to-end speedup from this promotion alone. Its concrete
improvement is the emitted primitive representation, supported by body
measurements; remaining entry and host-compilation behavior still matters.
The [production bytecode dump](investment-after-results/production-loop-bytecode.txt)
confirms primitive locals and checked `(JJ)J` addition with ordered transfer
temporaries. It is actual candidate output, not just the experimental rewrite.

After additional warmup, a tiny baseline body takes 48–67 ns but installed
session entry 400–840 ns, allocating 1,689–2,177 bytes/call versus about
49 bytes in the body variant. The baseline conservatively retains dynamic
context bindings (`:context-only? false`). Reusing the existing strict scalar
context-admission analysis is a candidate next step; collection/callback code
cannot receive that permission merely from observing scalar arguments.

First-loop preparation remains 10.11–19.21 ms including bootstrap, and the
paired estimate still repays that incremental cost after two large T0 calls.
This excludes compiler loading, and the latter runs cannot be used to revise
the earlier cold-loader cohort by subtracting timings from different runs.
Vector-state code remains near SCI at the small size; captured closure calls
and baseline HOF rewriting remain unsupported.

Full core checks after promotion: 221 tests, 6,902 assertions. Verification:
141 tests, 3,490 assertions. Both pass. The new regression checks mixed numeric
layouts, representation-sensitive results, simultaneous swaps, ordered entry
failures and overflow against T0. Existing tampered-plan and pinned-world tests
also pass. This remains a tested implementation bridge, not a new universal
proof of Clojure/JVM lowering.

## Investment model and next steps

For a measured installed candidate, use paired full-call savings:

`expected remaining valid calls × expected saving per call − preparation cost`.

The validity horizon matters as much as call count. World replacement, input
guard misses, compilation failures and installation refusals can all shorten
it. When estimating from bodies instead, include guard cost and miss overhead:
with hit probability `q`, old cost `T`, body cost `K`, guard cost `g` and extra
miss cost `m`, expected per-call saving is `q(T−K)−g−(1−q)m`. Do not subtract
guard cost again when it is already included in a full-call measurement.

This is a policy model, not a safety argument. Observed types can propose a
guarded specialization; static analysis, annotations or proof may establish
facts without that guard. Ansatz can justify stronger transformations while
also consuming investment. Resource policy should separately track latency,
CPU, retained code/memory and shared-VM costs. An isolated world does not
isolate JVM GC or compiler threads.

The resulting implementation order is:

1. Completed: promote validated direct-loop lowering and check its installed
   performance; retain entry overhead and warmup as explicit remaining costs.
2. Make the transfer producer and its selection policy world-managed, initially
   retaining stepped execution for unreviewed policies and independent checks
   on their outputs. Preserve old pinned worlds.
3. Expose bounded, binder-safe source inspection and construction; separate
   cheap control summaries from callee emission.
4. Share invariant/layout facts across static analysis and guarded feedback.
   Hoist justified checks out of loops, retaining exception/overflow behavior.
5. Add a conservative measured sponsor, candidate reuse and explicit failed
   investment accounting, before attempting autonomous broad optimization.

Typed Clojure-style inference is a possible fact producer, not a dependency
introduced by these experiments. Stronger proofs and direct bytecode emission
remain compatible extensions rather than prerequisites for this first gain.

## Reproduction and provenance

```sh
for process in 0 1 2; do
  clojure -J-Xmx1g -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"] :deps {org.babashka/sci {:mvn/version "0.15.59"}}}' \
    -M -m baseline.investment "$process"
done
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m baseline.investment-summary
```

Use the same three-process command with `baseline.loop-emission` for the body
experiment, and without the SCI dependency with `baseline.cold-preparation`
for lazy loading. `baseline.inspect-loop` dumps classes under `target/` for
`javap -p -c -classpath target/investment/classes '<class from classes.edn>'`.

The summarizer requires identical source/runtime/workload cohorts. The main
and body runners reject source changes during measurement. Original data are
in `investment-results`; the three source files changed by promotion are also
preserved there under `before/`. Restore those copies in an isolated checkout
to reproduce the original emitter. Running against current sources measures
the promoted path. Later results must remain a separate cohort.

The subsequent world-managed-service milestone changes compiler orchestration,
not these recorded cohorts. `investment-after-results/source/` preserves the
three modified production files at the measured direct-loop version, checked
against its source fingerprints. For strict historical source identity, use the
recorded manifest, including its source-file set; later added unused sources
are not part of that cohort. See the [current architecture](../../doc/engineering/compiler.md)
for staged service selection and its separate transition-count example.
