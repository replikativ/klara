# Status

The nucleus implements layers L0 to L5 of the [design](design/00-model.md)
at a deliberately small scope. Everything listed as implemented is covered
by the [conformance cases](spec/cases/), the [examples](examples/) or the
[tests](test/klara/); `clojure -M:test` runs all of them.

## Implemented

| Layer | What works | Limits |
|---|---|---|
| L0 Core | Clojure surface via host macros, destructuring, multi-arity and variadic fns, `loop`/`recur`, `letfn`, `try`/`catch`/`finally`, interop, `defmacro`, `case`; proper tail calls; closures capture only free locals | `defrecord` makes a host record class (no protocol implementations); no `deftype`/protocols, `binding`, `eval`; host lazy seqs call Klara functions in nested machines |
| L1 Worlds | Immutable worlds, late binding, pinned functions, `world/in`/`get`/`define`/`publish!`/`advance`, deltas and conflict detection, footprint slices, bounded history, `ns`/`require` with aliases and refers | No durable storage; reload of an already loaded namespace is not supported |
| L2 Staging | `code`/`esc`/`lift`/`run`/`reify`, fresh names, implicit cross-stage persistence, late and pinned links, dynamic extrusion check, Code views | No let-insertion; guarded links exist in the semantics but are not yet produced by the compiler |
| L3 Effects and jobs | Deep multi-shot handlers, default handlers, jobs with forked worlds, step budgets, nested reservation, deferred printing, adopt, resume, host-mutation refusal, parallel jobs (`run-all`), jobs without profiling | No first-class affine resources; only printing and definitions are isolated effects |
| L4 Compilation | Profiles; preparation as a job; the definitional checker with premises, speculation (assumptions, value guards), data definitions, fixpoint induction for loops against recursive definitions; certificates (ansatz, in-place ownership); lowering to JVM code with frame states, leaves as values, OSR, direct calls, host loops, hints as guards, arrays without reflection; compiled code in the world with provenance; precompilation from saved profiles; effect classes (L4.facts.effect) | Lowering excludes `try`, interop, `letrec` and effects outside speculation; Clojure forms as host IR (loops outside return position cost a closure; a direct bytecode backend is planned) |
| L5 Guest compiler | Klara code: `klara.jit` (specializers; the default is a staged interpreter that generates code from profiles, design/08), rules that extend it (`klara.jit.rules`, user rules such as `showcases/regex.clj`), `klara.own` (in-place), `klara.investor` (tiers by interpreted time spent, callees first, parallel exploration, steady-state measurement in jobs, net-gain decisions kept in the world, an opt-in trigger between forms) | Libraries cannot yet add to the world's rule set from their own namespace; vectorization and primitive representations are measured, not built (design/09) |
| Lifetimes | Named roots, footprint slices, deltas instead of parent references, per-candidate class loaders, retention report; collectability tests and a soak test | Retention is reported, not charged |

## Known gaps in the guarantees

- **Host functions are trusted.** A `clojure.core` function the prelude does
  not override (for example `spit` or `rand`) runs directly: inside a job it
  is not deferred. Printing, atoms and volatiles are overridden. Interop
  calls and array writes on objects from outside a job are not refused
  (`L3.job.host-mutation`), so jobs isolate only code that avoids them; the
  investor therefore measures only definitions whose effects a job
  contains (`L4.facts.effect`, up to `:handled`), and the effect analysis
  treats any function it cannot see as outside.
- **Unproved checker rules.** Most of the checker is specified and tested,
  including adversarially (`test/klara/adversarial_test.clj`), not proved:
  speculation (`speculate-assume`, `speculate-value`), fixpoint induction
  (`L4.check.fix`), `bool-let`, `commute`, `let-app`, data definitions,
  `self`, constants and the ownership judgment (`L4.check.in-place`, whose
  erasure theorem is open). The proved head rules hold for the formal
  fragment's form of each rule; spec/formal/README.md maps theorems to
  rules.
- **Lowering is trusted.** It is tested differentially (generated programs
  under stress, with the default specializer) and adversarially, not
  proved.
- **Class unloading depends on soft references.** Clojure's compiler caches
  generated classes softly; candidates' classes are reclaimed promptly only
  with `-XX:SoftRefLRUPolicyMSPerMB=0` (set for the test alias).
- **`finally` and discarded continuations.** A handler that drops its
  continuation skips `finally` blocks inside it (`L0.eval.exception`).

## Verification

[spec/formal](spec/formal/README.md) holds a kernel-checked semantics of a
Core fragment (integers, functions, recursion, late and pinned links,
handlers by operation name, staging) with determinism, preservation,
progress and safety proved in ansatz. The CEK machine is compared with it
differentially on generated programs and the conformance corpus, through
the real reader and expander (`clojure -M:formal:test-formal`, 500 generated
programs by default; with `KLARA_DIFF_SEEDS=5000`, 10003 of 10003 forms
agreed when last run). The `:formal` alias needs an ansatz checkout next to
this repository (`../ansatz`). The comparison found and fixed a
Clojure subtraction inconsistency and a missing not-a-function rule.

The checker's head rules, in the fragment's form, are proved to be steps of the semantics, and a
step is proved to preserve the terminal configurations reached
(`spec/formal/src/klara/formal/checker.clj`). Candidates the definitional
checker cannot relate can carry a certificate: the ansatz certifier quotes
the actual terms, states their equivalence for 64-bit integers and checks
the proof with the kernel; the assumption becomes a runtime guard
(L4.check.certificate). Klara programs can search for proofs in budgeted
jobs through `klara.proof/certify` (`spec/formal/cases/proof_search.clj`).

Not yet proved: rewriting under binders (contextual equivalence),
`L4.check.let-app`, the CEK machine's refinement of `step` (tested), and the
named-Core-to-Tm bridge (tested). Certificates cover unary integer
functions; the prototype's affine/ownership fragment and its proof models
are not yet ported.

## Performance

Are We Fast Yet? subset (`clojure -M:awfy`, each benchmark in its own JVM,
after the investor has run; design/07-performance.md has the history and
what each step taught). Klara compiled against Clojure on HotSpot, same
machine, under load (2026-11-01):

| Benchmark | Clojure (ms) | Klara compiled (ms) | Klara / Clojure |
|---|---|---|---|
| Mandelbrot | 40 | 54 | 0.8–1.3 (noisy) |
| Sieve | 0.0164 | 0.0187 | 1.1 |
| Towers | 0.748 | 0.757 | 1.0 |
| List | 0.061 | 0.102 | 1.7 |

What remains on List is the cost of a call between compiled definitions
(about 24 ns against 2 ns for a Clojure call). The interpreter is a CEK
machine with first-class, multi-shot continuations, 500–1300× slower than
V8; compiled code is what makes Klara usable.

`clojure -M:bench` compares the interpreter, compiled Klara, SCI and Clojure
on micro benchmarks in one JVM: good for finding cliffs, not for
publication. The interpreter pays for frames that SCI does not have and
runs at 2 to 13 times SCI (from 50–190 times before these):

- Terms are prepared once into nodes with slot environments, resolved host
  functions and inline caches for globals keyed by world id
  (`klara.runtime.prepare`).
- The driver keeps its state in a register array, evaluates immediate
  nodes without frames, and is split into small step functions: the
  single large driver exceeded the JVM's huge-method limit and was never
  JIT-compiled.

Next: a direct bytecode backend (design/07-performance.md, path step 3),
then vectorized reductions with a reassociation opt-in and overflow
certificates (design/09-extensions.md, step 5).
