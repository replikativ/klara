# Plan for this iteration

The order of work for landing the speculation design
([06-speculation.md](06-speculation.md)) and the showcase programs that
validate it. Each phase adds spec rules first, then implementation, then
tests citing the rules; `clojure -M:test`, `clojure -M:formal:test-formal`
and `clojure -M:bench` stay green at every commit. Progress is recorded here.

## Phases

- [x] **P1. Frame states, leaving compiled code, stack traces.** Done:
  A-normal form, frame states at every leave point, leaves for speculation,
  callee effects and budgets, call sites adding frames, Klara stack traces;
  stress mode (1500 generated programs agree); `speculate-sound` proved.
  On-stack replacement after a leave landed with P3b.
  Originally:
  Compiled code is normalized so that every point where it may leave has a
  frame state (the interpreter node to continue at, its environment, the
  enclosing frames). It leaves for: a failed speculation
  (`(if guard specialized reference)`), a callee effect (the nested machine's
  state is spliced into the caller's, no re-execution), and budget
  exhaustion (the job suspends at that call). Frames from compiled callers
  are added as the leave unwinds. Klara errors carry Klara stack traces with
  source positions. Validation: a deopt-stress mode that leaves at random
  points, compared with the interpreter on generated programs and the
  conformance corpus. Proof: the speculation rule.
- [x] **P2. Profiles.** Done: entries (argument classes and stable values,
  including loop iterations), callees, branches; `klara.profile/snapshot`;
  overhead within noise on the benchmark. Originally: Prepared nodes record argument classes, stable
  values, call targets, branch counts, collection shapes;
  `klara.profile/snapshot` returns them as data. Overhead under 10% on the
  benchmark.
- [ ] **P3a. Specializers.** Done: `klara.jit` (a Klara library over a few
  runtime functions): `context` (`:reference`, `:profile`, `:runtime`,
  `:specializer`), `function`, `guard`, `same?`, `stable?`/`stable-value`,
  `compile!`; `^{:klara/specialize f}`; value speculation in the checker
  (L4.check.speculate-value); showcase 1. Open: `:facts`, `:budget` and
  accounting, representation hints, specializers composing.
  Originally: The extension point of the JIT: a pure Klara
  function of a context (`:reference`, `:profile`, `:facts`, `:runtime`,
  `:budget`) and the default specializer, returning Code or declining.
  `jit/guard`, `jit/arg`, representation hints; checking; accounting;
  attached with `^{:klara/specialize f}`.
- [ ] **P3b. The default specializer.** Done (in Klara, `klara.jit/default`):
  cold-branch speculation, inlining of hot small definitions; lowering of
  immediately applied functions as `let`; on-stack replacement after a
  leave; compiled code under mints when it creates no escaping closures;
  showcase 2. Measured: long speculation buys nothing on HotSpot (see
  06-speculation.md §4), so it is dropped. Open: stable-value
  specialization in the default, monomorphic higher-order callees.
  Originally: A stage-polymorphic interpreter for
  Core written in Klara: inlining of monomorphic calls, speculation on long
  arithmetic, specialization on stable values, loops.
- [ ] **P4. Facts and guard discharge.** Done: guard discharge at call
  sites by specializing calls to known arguments (`specialize-known-calls`
  in the default, `jit/simplify`); data definitions as premises
  (L4.check.delta-data); the checker no longer unrolls loops when
  beta-reducing; intrinsics callable from host code. Showcase 1's driver
  specializes its call away. AOT given a saved profile (`run --record`,
  `run --aot`, `showcases/ahead_of_time.clj`: first run 1 s interpreted,
  0.12 s compiled ahead). Open: facts from type systems.
  Originally: The facts interface; a built-in
  checker for literal and checked-arithmetic types; ansatz certificates;
  discharge at call sites; AOT given a saved profile.
- [ ] **P5. The investor.** Done (v1, `klara.investor`, Klara code): per
  definition, gate on work (loop iterations count), prepare alternatives
  (`:as-is`, `:default`, `:attached`) in parallel jobs (`job/run-all`,
  L3.job.parallel), measure each at steady state on a profile sample in a
  job that does not train profiles (L3.job.profile), install the best net
  gain (as many calls again expected; savings within 10% count as none),
  account for everything; `showcases/investor.clj`. Caches are single-entry
  so parallel jobs on different worlds cannot mix them. Open: proof-carrying
  alternatives (needs the arithmetic certifier), decisions kept in a world,
  automatic triggering.
  Originally: A Klara policy over profiles and measured
  costs: threshold and cost table first, parallel exploration in forks,
  honest accounting, declining when it does not pay.
- [x] **P6. Ownership, functional but in-place.** Done: the ownership
  judgment and erasure check (`klara.compile.own`, the `:in-place`
  certifier, L4.check.in-place); erasure-tolerant owned updates and freezing
  at leaves, so multi-shot continuations stay correct; the recipe in Klara
  (`klara.own/in-place`); the investor's `:in-place` alternative;
  `showcases/in_place.clj` (17x faster, 180x less allocation; the escaping
  variant refused). Open: the erasure theorem in ansatz, the judgment
  verified in ansatz.
  Originally: Uniqueness judgment,
  erasure, transient lowering, the accumulator recipe; the erasure theorem.

## Showcase programs

Each is a short Klara program in `showcases/`, run with
`clojure -M:klara run showcases/...`, printing a short report (outcome,
evidence, guards, time, allocation), and run as a test.

1. **An interpreter becomes a compiler at run time** (P1–P3a). Done as
   `showcases/interpreter_to_compiler.clj` with an arithmetic interpreter
   (30× once its driver is compiled; the unguarded variant is rejected); a
   regex matcher is the next instance. A regex
   matcher written as an interpreter, with a user-written specializer: once
   the profile shows a stable pattern, the JIT stages the matcher for it,
   guarded on the pattern; checked by the kernel.
2. **Speculate, fail, keep going** (P1–P3b). Done as
   `showcases/speculate_fail_continue.clj`: a ledger loop with a rare
   refund that performs an effect; rejected without speculation, 23× with
   it, one leave, one review, re-entry into compiled code, retirement on a
   helper change, old world keeps its code. (The plan said longs; measured
   to be pointless on HotSpot, the cold effectful branch is the real case.)
   Originally: A numeric kernel specialized
   to longs from its profile; a double halfway through a large input fails
   the guard inside the loop and the interpreter continues at that
   iteration; redefining a helper invalidates the compiled code while an old
   world keeps its own.
3. **Proofs where they pay** (P4–P5). Polynomial scoring: the investor plans
   fusion (definitional), Horner's rule (certificate under a range guard)
   and long arithmetic (speculative); rejected without the premise.
4. **Functional but in-place** (P6). Done as `showcases/in_place.clj`. A persistent `frequencies`-style loop;
   the investor chooses a transient accumulator, allocation drops, erasure
   checks it, and it refuses when the accumulator escapes.

## Later

Equality saturation for pure regions; a JavaScript host; machine learning
workloads (models as candidates with data-evaluated evidence). Durable
world and investor state on [Datahike](https://github.com/replikativ/datahike),
copy-on-write storage through yggdrasil's protocols, and a merge with
spindel's forkable reactive runtime model.
