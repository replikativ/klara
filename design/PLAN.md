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
  sites by specializing calls to known arguments (first as rewrite passes
  in the default; since P7.6 the staged interpreter unfolds known calls,
  and `compiler/specialize` compiles a function for known arguments); data definitions as premises
  (L4.check.delta-data); the checker no longer unrolls loops when
  beta-reducing; intrinsics callable from host code. Showcase 1's driver
  specializes its call away. Precompilation from a saved profile (`run --record`,
  `run --precompile`, `showcases/precompiled.clj`: first run 1 s interpreted,
  0.12 s compiled ahead). Open: facts from type systems.
  Originally: The facts interface; a built-in
  checker for literal and checked-arithmetic types; ansatz certificates;
  discharge at call sites; precompilation given a saved profile.
- [ ] **P5. The investor.** Done (v1, `klara.investor`, Klara code): per
  definition, gate on work (loop iterations count), prepare alternatives
  (`:as-is`, `:default`, `:attached`) in parallel jobs (`job/run-all`,
  L3.job.parallel), measure each at steady state on a profile sample in a
  job that does not train profiles (L3.job.profile), install the best net
  gain (as many calls again expected; savings within 10% count as none),
  account for everything; `showcases/investor.clj`. Caches are single-entry
  so parallel jobs on different worlds cannot mix them. Later: tiers by
  interpreted time spent, automatic triggering between forms, promotion of
  baseline code (L4.jit.tiers, L4.jit.trigger); callees decided first,
  ties to as-is, measuring after the host's JIT is idle; decisions kept in
  the world (`investor/decisions`); measuring in jobs whatever a job
  contains (L4.facts.effect). Open: proof-carrying alternatives (needs the
  arithmetic certifier).
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

- [ ] **P7. The staged JIT** ([08-staged-jit.md](08-staged-jit.md)). One
  interpreter for Core in Klara with two binding times, replacing the
  default specializer's tree rewrites and the separate partial evaluator.
  Each step adds its spec rules, tests citing them, and keeps the suite,
  the stress tests (generated programs through the default specializer) and
  the benchmarks at least as good as before:
  1. [x] **Total views.** Every construct has a view (multi-arity and variadic
     functions, letrec, throw, try, interop, def, perform, handle, code
     templates and holes); `:other` disappears (L2.view.total).
  2. [x] **Binding times and the domain.** `static`/`dynamic`/`reify`, the
     environment, the domain interface; the generator instantiated with
     values is an interpreter, tested against the machine on the
     conformance corpus and generated programs.
  3. [x] **Core constructs.** const, local, global (data definitions static),
     if, let, do, fn (fresh binders through templates), app (pure host
     functions computed, known functions unfolded within the budget), loops
     and recur; residuals checked by the kernel.
  4. [x] **Facts from profiles.** Cold branches, stable values, monomorphic
     call sites, each emitted as a speculation whose fallback is generated
     with everything dynamic (no splicing of open reference code).
  5. [x] **Everything else dynamic.** try, interop, letrec, def, code and
     several arities kept whole (their free locals substituted); the checker
     relates them part by part (L4.check.alpha, L4.check.code). perform and
     handle are surface macros over host calls, so they need nothing here.
  6. [x] **Switch.** The staged interpreter becomes `jit/default`; the rewrite
     passes and `recipes/inline` are removed; showcases, awfy and the
     investor run on it; `code/make` is no longer used by specializers.
  7. **Proof (later).** Partial-evaluation correctness of the generator for
     the formal fragment; and the checker's fixpoint rule (L4.check.fix:
     a loop against a recursive definition, by Scott induction), trusted
     until then.

- [x] **P8. Extending the JIT** ([09-extensions.md](09-extensions.md),
  section 5). Rules as user extensions of the staged interpreter
  (L4.jit.rules); the investor's measuring made trustworthy (callees first,
  ties to as-is, waiting for the host's JIT, a host loop for batches, a JVM
  per benchmark); class speculation as the first built-in rule
  (L4.jit.class-hints) and arrays without reflection (L4.lower.arrays);
  effect classes (L4.facts.effect); the regex matcher as a user rule
  (`showcases/regex.clj`), with fixpoint induction, `bool-let` and
  `commute` in the checker and `recur` across template holes
  (L2.code.recur). Step 5 (primitive loops, vectorization) measured, not
  built. Open: how a library adds to `klara.jit/rules`, relative effects
  resolved at call sites.
- [ ] **P9. Publication landing.** Consistency before collaborators read
  it. Soundness fixes from a spec audit, each with an adversarial test: a
  named preparation's reference must mean that definition
  (L4.prepare.reference); unfolding and `reify` keep captured atoms as
  references (L4.check.delta, L2.reify.fn); scalars compared by host
  `equals` (L4.check.const, `same?`); the effect analysis outside for
  anything it cannot see (L4.facts.effect). Proof claims mapped theorem by
  theorem to the rules they cover (spec/formal/README.md); prose and spec
  brought up to date with the code.

## Next iteration

A direct bytecode backend (07-performance.md, path step 3): the subset
lowered today, emitted as hidden classes with explicit context, primitive
signatures and real loops, designed to become the first backend of a
checked low-level IR. Then vectorized reductions (09-extensions.md, step 5)
with a reassociation opt-in and overflow certificates.

## Showcase programs

Each is a short Klara program in `showcases/`, run with
`clojure -M:klara run showcases/...`, printing a short report (outcome,
evidence, guards, time, allocation), and run as a test.

1. **An interpreter becomes a compiler at run time** (P1–P3a). Done as
   `showcases/interpreter_to_compiler.clj` with an arithmetic interpreter
   (30× once its driver is compiled; the unguarded variant is rejected); the
   regex matcher is the second instance, `showcases/regex.clj`, with the
   staged matcher as a user rule (design/09-extensions.md). A regex
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
3. **Proofs where they pay** (P4–P5). The investor part is done
   (`showcases/investor.clj`). The proof part, Horner's rule under a range
   guard as a certified alternative, has its first building blocks proved
   (`ev-prim-lit`, `ev-prim-l`, `ev-prim-r`, `step-of-ev`: a step inside
   nested arithmetic), but is blocked on bounding nonlinear intermediates
   (`i*i <= 2^40` from `|i| <= 2^20`): ansatz has no `nlinarith`, and
   `linarith` over the product of the bounds did not finish. Next: a
   nonlinear tactic in ansatz, or a reflected arithmetic evaluator proved
   once. (The plan said "long arithmetic" as the speculative step; it is
   pointless on HotSpot, see 06-speculation.md §4.)
   Originally: Polynomial scoring: the investor plans
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
