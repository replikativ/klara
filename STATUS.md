# Status

The nucleus implements layers L0 to L5 of the [design](design/00-model.md)
at a deliberately small scope. Everything listed as implemented is covered
by the [conformance cases](spec/cases/), the [examples](examples/) or the
[tests](test/klara/); `clojure -M:test` runs all of them.

## Implemented

| Layer | What works | Limits |
|---|---|---|
| L0 Core | Clojure surface via host macros, destructuring, multi-arity and variadic fns, `loop`/`recur`, `letfn`, `try`/`catch`/`finally`, interop, `defmacro`, `case`; proper tail calls; closures capture only free locals | `defrecord` as tagged maps (no protocol implementations); no `deftype`/protocols, `binding`, `eval`; host lazy seqs call Klara functions in nested machines |
| L1 Worlds | Immutable worlds, late binding, pinned functions, `world/in`/`get`/`define`/`publish!`/`advance`, deltas and conflict detection, footprint slices, bounded history, `ns`/`require` with aliases and refers | No durable storage; reload of an already loaded namespace is not supported |
| L2 Staging | `code`/`esc`/`lift`/`run`/`reify`, fresh names, implicit cross-stage persistence, late and pinned links, dynamic extrusion check, Code views | No let-insertion; guarded links exist in the semantics but are not yet produced by the compiler |
| L3 Effects and jobs | Deep multi-shot handlers, default handlers, jobs with forked worlds, step budgets, nested reservation, deferred printing, adopt, resume, host-mutation refusal, parallel jobs (`run-all`), jobs without profiling | No first-class affine resources; only printing and definitions are isolated effects |
| L4 Compilation | Profiles; preparation as a job; the definitional checker with premises, speculation (assumptions, value guards), data definitions; certificates (ansatz, in-place ownership); lowering to JVM code with frame states, leaves as values, OSR, direct calls, host loops, hints as guards; compiled code in the world with provenance; AOT from saved profiles | Lowering excludes `try`, interop, `letrec` and effects outside speculation; Clojure forms as host IR (loops outside return position cost a closure) |
| L5 Guest compiler | Klara code: `klara.jit` (specializers, the default specializer: cold-branch speculation, known-call specialization, inlining), `klara.own` (in-place), `klara.investor` (parallel exploration, steady-state measurement, net-gain decisions) | No automatic triggering; decisions are not kept in a world yet |
| Lifetimes | Named roots, footprint slices, deltas instead of parent references, per-candidate class loaders, retention report; collectability tests and a soak test | Retention is reported, not charged |

## Known gaps in the guarantees

- **Host functions are trusted.** A `clojure.core` function the prelude does
  not override (for example `spit` or `rand`) runs directly: inside a job it
  is not deferred, and if a compiled call is abandoned and re-executed it
  runs twice. Printing, atoms and volatiles are overridden. Classifying host
  functions as pure, effectful or refused is open work.
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
the real reader and expander (`clojure -M:formal:test-formal`; 10003 of
10003 forms agreed over 5000 programs). The comparison found and fixed a
Clojure subtraction inconsistency and a missing not-a-function rule.

The checker's head rules are proved to be steps of the semantics, and a
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

Are We Fast Yet? subset (`clojure -M:awfy`, ms per iteration, see
design/07-performance.md): Mandelbrot node 24 / Clojure 27 / Klara
compiled 79; Sieve 0.010 / 0.008 / 0.33; Towers 0.065 / 0.25 / 0.77;
List 0.013 / 0.033 / 0.51. The interpreter is 400-1000x slower than V8.

Older micro benchmarks (`clojure -M:bench`):

`clojure -M:bench` runs the same programs in Klara (interpreted), Klara
(compiled with `optimize!`), SCI and Clojure. One JVM, best of seven: good
for finding cliffs, not a publication benchmark. Times in milliseconds:

| Program | Klara | Klara compiled | SCI | Clojure |
|---|---|---|---|---|
| fib 20 | 38.5 | 1.5 | 3.0 | 1.3 |
| loop to 100,000 | 20.8 | 4.9 | 10.9 | 2.7 |
| closures | 40.8 | 4.8 | 15.2 | 3.4 |
| let-heavy | 26.8 | 3.9 | 12.5 | 1.9 |
| maps | 16.8 | 2.5 | 8.1 | 2.4 |

The interpreter is a CEK machine with first-class, multi-shot
continuations, so it pays for frames that SCI does not have; it runs at 2
to 13 times SCI. Compiled code is faster than SCI and close to Clojure.
What made the difference (from 50-190 times SCI):

- Terms are prepared once into nodes with slot environments, resolved host
  functions and inline caches for globals keyed by world id
  (`klara.runtime.prepare`).
- The driver keeps its state in a register array, evaluates immediate
  nodes without frames, and is split into small step functions: the
  single large driver exceeded the JVM's huge-method limit and was never
  JIT-compiled. Hot namespaces warn on reflection.
- Compiled code calls itself directly (its own generation is a premise),
  calls other candidates without a nested machine, and caches late links
  per call site.

Next: tiering as an explicit policy (compile after a threshold), the
remaining interpreter costs (frames for non-tail calls, argument vectors),
and primitive arithmetic in compiled code.
