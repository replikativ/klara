# Effect handler costs on the JVM (Klara prototype)

Question: Klara core v1 §1 has `perform` and deep `handle`. Continuations are
one-shot by default and multi-shot only when they capture no resources. The
JVM has no first-class continuations. Can `perform` cost close to a plain call
in the common (tail-resumptive, A-O8) case? And what do one-shot and
multi-shot resumption cost?

Short answer: yes for the fast path. A ThreadLocal evidence vector costs
1.2–1.4x a direct call on C2, as long as the clause call site stays
monomorphic. Selective CPS (partial-cps) gives general one-shot and multi-shot
continuations at about 3x a direct call per perform. Multi-shot enumeration by
CPS costs 1.65x a hand-written DFS. Loom's internal `Continuation` works, but
at about 250 ns per perform it is unusable for fine-grained effects, and it
cannot be multi-shot.

## Layout

| file | content |
|---|---|
| `src/klara/fx.clj` | direct-style fast path: `defop` (op id fixed at definition time), `perform`/`handle` over a ThreadLocal evidence vector, plus variants with a global array, a ScopedValue, a dynamic var with a map, and a linked-list stack. Also abortive handlers with a preallocated stackless exception. |
| `src/klara/cps.clj` | general continuations: partial-cps `invert` with `perform` as the only breakpoint. Clauses are `(fn [arg k])`. `k` may be called 0, 1 or n times. |
| `src/klara/loom.clj` | one-shot deep handlers on `jdk.internal.vm.Continuation` (needs `--add-exports java.base/jdk.internal.vm=ALL-UNNAMED`) |
| `src/klara/work.clj` | ops and the unit of work (one xorshift-multiply step on a mutable field, ~5 cycles of dependent latency) |
| `src/klara/hmm.clj` | 20-step 2-state HMM (20 binary choices, 40 performs per run, 2^20 paths), written once as a macro template and instantiated per style. Handlers: importance sampling (direct, fast, cps, loom), exact enumeration (direct DFS, cps multi-shot, replay), and SMC with systematic resampling (cps multi-shot, replay with abort) |
| `src/klara/bench.clj` | benchmark registry and harness |
| `run.sh`, `summarize.clj` | driver: one JVM per benchmark, rounds interleaved. Summary table. |
| `results/raw-*.edn` | raw output, one EDN line per JVM run, with every sample |
| `results/summary.md` | generated tables |

Correctness: all enumeration variants give log Z = −14.23463437300903, which
matches the forward algorithm (−14.234634373008753). IS and SMC give the same
estimates across styles, because they consume the same RNG stream: IS
−14.27, SMC −14.22.

## Method

- **Machine:** Intel Core Ultra 7 258V (Lunar Lake). Cores 0–3 are P-cores
  (4.7–4.8 GHz max) and cores 4–7 are LP E-cores (3.7 GHz). 32 GB RAM, Linux
  7.0. Benchmarks were pinned with `taskset -c 1-3`.
- **Noise:** this was not a quiet machine. The governor was `powersave` with
  EPP `power` and `platform_profile=low-power`, so the cores ran at about
  1.4–1.5 GHz. Load average was 9–18 from other JVMs and agents on the box.
  Absolute ns are therefore about 3x what a performance-profile machine would
  show. **Read the ratios, not the absolute ns.** Even a pure primitive loop of
  the work step measured 4.6 ns/step.
- **JVMs:**
  - Primary: OpenJDK 25.0.4.1 (Ubuntu build), C2. 3 rounds.
  - Secondary: Oracle GraalVM 25.0.1 with the Graal JIT. 2 rounds. The
    table below shows round 1; `results/summary.md` has both rounds, and
    round 2 changed best values by at most a few percent.
  - Flags: `-Xms1g -Xmx1g -XX:+UseParallelGC --add-exports java.base/jdk.internal.vm=ALL-UNNAMED`.
  - Clojure 1.12.0, partial-cps at `ed9b382` (local root).
- **Harness:** one fresh JVM per benchmark per round, so call-site profiles do
  not pollute each other. Each run warms up for ≥ 3 s (≥ 5 calls). It then
  takes 15 samples of ≥ 200 ms each and records ns per op. Results go to a
  volatile sink.
  - "best" = the minimum over all samples and rounds. This is the estimate of
    intrinsic cost under contention.
  - "median" = the median over rounds of the per-run medians.
  - Slowdown = best / best of the baseline.
- **Workloads:**
  - (i) a loop of 10^7 `perform tick 1`. The Loom variant uses 10^6.
  - (ii) the HMM. Units are ns per program run (one particle or one
    enumerated path), with 1000 particles per call. Enumeration covers all
    2^20 paths per call.
  - (iii) handle frames whose op is never performed.
  - Abort runs 10^6 iterations, each throwing through 0 or 10
    non-inlinable frames.

## Results: OpenJDK 25, C2 (3 rounds)

### (i) counter effect, 10^7 performs

| strategy | best ns/perform | median | vs direct fn | vs protocol |
|---|---:|---:|---:|---:|
| direct fn call (baseline) | 3.93 | 4.01 | 1.00x | 0.86x |
| protocol call | 4.56 | 4.65 | 1.16x | 1.00x |
| fast path, global array (not thread-safe; lower bound) | 3.96 | 4.04 | 1.01x | 0.87x |
| **fast path, ThreadLocal evidence vector** | **5.36** | 5.47 | **1.36x** | **1.18x** |
| same, with 10 unrelated handlers installed | 5.35 | 5.46 | 1.36x | 1.17x |
| same, clause call site megamorphic (3 clause classes) | 30.46 | 31.75 | 7.74x | 6.68x |
| fast path, ScopedValue | 4.74 | 5.13 | 1.21x | 1.04x |
| fast path, `^:dynamic` var + map | 17.64 | 18.02 | 4.49x | 3.87x |
| linked-list handler stack, depth 0 | 5.58 | 5.72 | 1.42x | 1.22x |
| linked-list handler stack, 10 frames to skip | 21.84 | 22.39 | 5.55x | 4.79x |
| general one-shot, CPS (partial-cps) | 12.06 | 12.53 | 3.06x | 2.64x |
| general one-shot, Loom `Continuation` | 248.45 | 255.71 | 63x | 54x |

### (iii) unused handler frames

| case | best ns/iter | median | vs no frame |
|---|---:|---:|---:|
| no frame, 10^7 loop (baseline) | 3.96 | 4.01 | 1.00x |
| one fast-path frame for an unused op around the loop | 3.87 | 4.01 | 0.98x (free) |
| fast path: `perform` reachable but never executed | 3.91 | 4.01 | 0.99x (free) |
| **CPS: `perform` reachable but never executed** | 10.65 | 11.03 | **2.69x** |
| no frame, 10^6 loop (baseline, noisy: medians 2.1–4.1) | 1.66 | 3.98 | 1.00x |
| fast-path frame installed per iteration | 14.99 | 15.32 | ~ +11 ns/frame |
| abort frame (try/catch + token) per iteration | 17.43 | 18.36 | ~ +14 ns/frame |
| CPS frame (`handle` + `run` of a perform-free body) per iteration | 18.53 | 19.15 | ~ +15 ns/frame |
| ScopedValue frame per iteration | 34.10 | 55.19 | ~ +30–50 ns/frame |
| Loom frame (new `Continuation`, never yields) per iteration | 114.93 | 122.16 | ~ +115 ns/frame |
| `binding` frame per iteration | 219.67 | 230.64 | ~ +220 ns/frame |

### Abortive handlers (10^6 iterations)

| case | best ns/iter | median | vs normal return |
|---|---:|---:|---:|
| normal return through 10 frames (baseline) | 32.35 | 33.43 | 1.00x |
| stackless preallocated throw, handler in the same method | 68.18 | 70.52 | 2.11x |
| stackless preallocated throw through 10 frames | 520.38 | 541.12 | 16x |
| `ex-info` throw (captures stack) through 10 frames | 25336 | 25705 | 783x |

### (ii) HMM, 20 choices + 20 observes per run

| handler | mechanism | best ns/run | median | vs direct |
|---|---|---:|---:|---:|
| IS, hand-written direct (baseline) | none | 180.7 | 191.3 | 1.00x |
| IS, one-shot | fast path (ThreadLocal) | 480.6 | 514.4 | 2.66x |
| IS, one-shot | CPS | 712.7 | 814.8 | 3.94x |
| IS, one-shot | Loom | 9903.6 | 10194.0 | 54.8x |
| exact enumeration, hand-written DFS (baseline) | none | 44.8 / path | 45.8 | 1.00x |
| exact enumeration, **multi-shot** (k resumed twice per choose) | CPS | 73.8 / path | 76.5 | **1.65x** |
| exact enumeration by re-execution of a choice prefix | fast path + replay | 688.1 / path | 700.4 | 15.4x |
| SMC, 1000 particles, **multi-shot** (k resumed once per offspring) | CPS | 2580 / particle | 2804 | 14.3x of IS-direct; **4.6x faster than replay** |
| SMC by re-execution, abort at the t-th observe | fast path + replay + stackless abort | 11923 / particle | 12342 | 66x of IS-direct |

Per-perform cost inside the HMM, as (handler − direct)/40:
- fast path: about 7.5 ns
- CPS: about 13 ns
- Loom: about 243 ns

The fast-path IS run carries costs the counter loop does not: boxing of the
choose result and unboxing of the observe argument through `IFn`, and two
different clauses.

### GraalVM 25 (Graal JIT), round 1 (both rounds in results/summary.md)

| benchmark | best ns | vs direct |
|---|---:|---:|
| direct fn / protocol | 2.63 / 3.15 | 1.00x / 1.20x |
| fast path, ThreadLocal / megamorphic / global | 5.74 / 6.66 / 5.34 | 2.18x / 2.53x / 2.03x |
| CPS one-shot | 11.16 | 4.24x |
| Loom | 351.7 | 134x |
| frame per iteration: fast / CPS / Loom (none-iter = 2.77) | 4.95 / 7.30 / 47.4 | — |
| abort: stackless d10 / ex-info d10 (ret = 5.94) | 311.5 / 15634 | — |
| HMM IS: direct / fast / cps / loom | 114 / 384 / 634 / 6048 | 1 / 3.4 / 5.6 / 53x |
| enum: direct / cps / replay | 20.8 / 62.5 / 548 | 1 / 3.0 / 26x |
| SMC: cps / replay | 1916 / 7578 | — |

Graal inlines the direct call better than C2: 2.6 ns against 3.9 ns. The fast
path then sits at about 2.2x direct, but only 1.8x the protocol call. Graal is
much more tolerant of the megamorphic clause site (2.5x where C2 shows 7.7x).
The full Graal tables are in `results/summary.md`.

## What did not work or is not covered

- **Loom multi-shot is impossible.** `jdk.internal.vm.Continuation` has no
  copy or clone. One-shot works on JDK 25 on a platform thread with
  `--add-exports`. It is an internal API with no compatibility promise.
- **Deep-handler re-routing is not implemented in the fast path.** A clause
  that performs its own op should reach the next outer handler. None of the
  benchmarked clauses do this. Koka handles it by keeping the outer evidence in
  the frame, which costs nothing unless the clause performs. This must be
  added before the fast path is semantically complete.
- **foerster/spindel savepoints were read but not benchmarked.** spindel's
  savepoint is a partial-cps continuation plus a copy-on-write world fork.
  `fork` copies world state and then resumes the same CPS continuation. So its
  multi-shot mechanism is the CPS row above plus the world-fork cost, which
  this prototype does not measure. The savepoint code lives on spindel's
  `feat/savepoints` branch.
- **Noise.** The median ranges in `results/summary.md` show occasional slow
  rounds; the worst outliers are 1.5–1.7x the best. `iii/none-iter` is
  bimodal, which makes per-frame costs good to about ±2 ns. The ranking of
  strategies was the same in every round.
- **The megamorphic row is a worst case.** On C2, 3 clause classes at one
  site cost 7.7x. Real programs where one perform site sees many handlers
  will sit somewhere between the monomorphic and megamorphic rows.

## Conclusions

**(1) Can the tail-resumptive fast path be within 2x of a protocol call?
Yes.**
- On C2 the ThreadLocal evidence vector is 1.18x a protocol call (1.36x a
  direct call).
- ScopedValue is 1.04x a protocol call.
- A non-thread-local array matches a direct call. The remaining cost is the
  ThreadLocal lookup.
- The lookup is independent of handler depth, because each op has a fixed slot
  assigned by `defop`. A linked-list stack grows with depth: 5.5x direct with
  10 frames to skip.
- The condition is that the clause call site stays monomorphic or bimorphic.
  When 3 clause classes reach one perform site, C2 falls to 7.7x direct
  (6.7x protocol). Graal holds at 2.5x.
- `binding` + map, the Clojure idiom, is 4.5x direct per perform and 130x per
  frame. Klara should not use it.

**(2) What does an unused handler frame cost?**
- A fast-path frame installed around hot code costs nothing measurable
  (0.98x).
- Installing one costs about 11 ns on C2 (try/finally, ThreadLocal get, two
  array stores) and about 2 ns on Graal.
- Abort and CPS frames cost about 14–15 ns. Loom frames cost about 115 ns,
  because each one allocates a Continuation. ScopedValue frames cost 30–50 ns.
- The larger hidden cost is in CPS-compiled code. Code from which a general
  `perform` is reachable pays 2.7x even when the perform never runs, because
  loops become trampolined continuations. Under selective CPS, "pay nothing
  when unused" holds for handler frames but not for code that might perform.

**(3) What do one-shot and multi-shot continuations cost, and which mechanism
should Klara use?**
- One-shot by CPS costs about 12 ns/perform (3x direct) in a tight loop, and
  4x direct on the whole IS program.
- Loom costs 250 ns/perform (60x) and 115 ns per frame, and cannot do
  multi-shot. It is only an option for coarse effects (I/O, blocking) and
  should be rejected for the core.
- Multi-shot by CPS is cheap. The continuation is an immutable closure, so a
  second resume costs one more call. Exact enumeration runs at 1.65x a
  hand-written DFS. SMC is 4.6x faster than re-execution, and enumeration is
  9x faster than re-execution.
- Replay is O(T) per resume, so it loses by a factor of about T/2: 15x on
  enumeration. It also requires deterministic re-execution.
- Abort should use preallocated stackless exceptions: 50x cheaper than
  `ex-info`, though still about 0.5 µs through 10 frames on C2.
- Recommendation:
  - tail-resumptive clauses: ThreadLocal or ScopedValue evidence vector with
    op ids fixed at definition time;
  - abortive clauses: stackless exceptions;
  - general and multi-shot clauses: selective CPS (partial-cps);
  - multi-shot with world state: spindel world fork on top of CPS.

**(4) Implication for the core design.**
- The per-call cost is decided by the handler clause. A clause that resumes
  once in tail position is a function call. This is A-O8, and it is checkable
  syntactically when the handler is defined.
- The compilation strategy is decided by the code that performs. Under
  selective CPS, a function either is CPS-compiled, paying about 2.7x even
  when it never suspends, or it cannot be resumed non-tail.
- So the property has to be known when the code that performs is compiled,
  not only when the handler is installed. Two workable designs:
  - **(a)** Classify each op at `defop` as `:tail`, `:abort` or `:general`.
    Track a "may perform a general op" bit in the effect row, so that only
    code reaching `:general` ops is CPS-compiled. State, reader, logging,
    `observe` and `factor` would be `:tail`. `throw` would be `:abort`.
  - **(b)** Compile both a direct and a CPS version of effectful code, as
    partial-cps's `async+sync` does, and pick one at `handle` time according
    to whether every installed handler for the reachable ops is
    tail-resumptive. This costs code size and adds a selection rule to the
    semantics.
- `choose` is the case that decides between them. It is tail-resumptive under
  importance sampling, where the fast path is 1.5x faster than CPS on the HMM,
  but general under enumeration and SMC.
- Option (a) alone forces every probabilistic program into CPS. Option (b)
  avoids that.
- I recommend (a) as the semantics, with an optimization in the spirit of
  (b) for ops declared `:general`. This is what a fast-path theorem like
  A-O8 should be stated against: a program in which every handler of the ops
  it reaches is tail-resumptive may run its direct compilation.
- The "multi-shot only without resources" rule fits CPS directly. The
  continuation is a closure, so the check is that it captures no linear or
  resource values. That is a property of the captured context, enforced at
  the point where a clause resumes `k` a second time.
