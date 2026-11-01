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
  Remaining: on-stack replacement (entering compiled loops mid-run).
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
- [ ] **P2. Profiles.** Prepared nodes record argument classes, stable
  values, call targets, branch counts, collection shapes;
  `klara.profile/snapshot` returns them as data. Overhead under 10% on the
  benchmark.
- [ ] **P3a. Specializers.** The extension point of the JIT: a pure Klara
  function of a context (`:reference`, `:profile`, `:facts`, `:runtime`,
  `:budget`) and the default specializer, returning Code or declining.
  `jit/guard`, `jit/arg`, representation hints; checking; accounting;
  attached with `^{:klara/specialize f}`.
- [ ] **P3b. The default specializer.** A stage-polymorphic interpreter for
  Core written in Klara: inlining of monomorphic calls, speculation on long
  arithmetic, specialization on stable values, loops.
- [ ] **P4. Facts and guard discharge.** The facts interface; a built-in
  checker for literal and checked-arithmetic types; ansatz certificates;
  discharge at call sites; AOT given a saved profile.
- [ ] **P5. The investor.** A Klara policy over profiles and measured
  costs: threshold and cost table first, parallel exploration in forks,
  honest accounting, declining when it does not pay.
- [ ] **P6. Ownership, functional but in-place.** Uniqueness judgment,
  erasure, transient lowering, the accumulator recipe; the erasure theorem.

## Showcase programs

Each is a short Klara program in `showcases/`, run with
`clojure -M:klara run showcases/...`, printing a short report (outcome,
evidence, guards, time, allocation), and run as a test.

1. **An interpreter becomes a compiler at run time** (P1–P3a). A regex
   matcher written as an interpreter, with a user-written specializer: once
   the profile shows a stable pattern, the JIT stages the matcher for it,
   guarded on the pattern; checked by the kernel.
2. **Speculate, fail, keep going** (P1–P3b). A numeric kernel specialized
   to longs from its profile; a double halfway through a large input fails
   the guard inside the loop and the interpreter continues at that
   iteration; redefining a helper invalidates the compiled code while an old
   world keeps its own.
3. **Proofs where they pay** (P4–P5). Polynomial scoring: the investor plans
   fusion (definitional), Horner's rule (certificate under a range guard)
   and long arithmetic (speculative); rejected without the premise.
4. **Functional but in-place** (P6). A persistent `frequencies`-style loop;
   the investor chooses a transient accumulator, allocation drops, erasure
   checks it, and it refuses when the accumulator escapes.

## Later

Equality saturation for pure regions; a JavaScript host; machine learning
workloads (models as candidates with data-evaluated evidence). Durable
world and investor state on [Datahike](https://github.com/replikativ/datahike),
copy-on-write storage through yggdrasil's protocols, and a merge with
spindel's forkable reactive runtime model.
