# Status

The nucleus implements layers L0 to L5 of the [design](design/00-model.md)
at a deliberately small scope. Everything listed as implemented is covered
by the [conformance cases](spec/cases/), the [examples](examples/) or the
[tests](test/klara/); `clojure -M:test` runs all of them.

## Implemented

| Layer | What works | Limits |
|---|---|---|
| L0 Core | Clojure surface via host macros, destructuring, multi-arity and variadic fns, `loop`/`recur`, `letfn`, `try`/`catch`/`finally`, interop, `defmacro`, `case`; proper tail calls; closures capture only free locals | No `deftype`/`defrecord`/protocols, `binding`, `eval`; host lazy seqs call Klara functions in nested machines |
| L1 Worlds | Immutable worlds, late binding, pinned functions, `world/in`/`get`/`define`/`publish!`/`advance`, deltas and conflict detection, footprint slices, bounded history, `ns`/`require` with aliases and refers | No durable storage; reload of an already loaded namespace is not supported |
| L2 Staging | `code`/`esc`/`lift`/`run`/`reify`, fresh names, implicit cross-stage persistence, late and pinned links, dynamic extrusion check, Code views | No let-insertion; guarded links exist in the semantics but are not yet produced by the compiler |
| L3 Effects and jobs | Deep multi-shot handlers, default handlers, jobs with forked worlds, step budgets, nested reservation, deferred printing, adopt, resume, host-mutation refusal | No first-class affine resources; only printing and definitions are isolated effects |
| L4 Compilation | Preparation as a job, the definitional checker with premises, lowering to JVM functions, executables with per-world validity, installation, deopt by re-execution, pinning (AOT), `specialize`, `optimize!`, `explain` | Lowering excludes `try`, interop, `letrec` and effects; no type-directed rewrites; synchronous preparation |
| L5 Guest compiler | `klara.compiler` API and the `inline` partial evaluator, both written in Klara | No policies or threshold scheduling yet |
| Lifetimes | Named roots, footprint slices, deltas instead of parent references, per-candidate class loaders, retention report; collectability tests and a soak test | Retention is reported, not charged |

## Not yet proved

No rule is mechanically proved. The checker rules (`L4.check.*`) are the
first targets for ansatz proofs against an L0 semantics; the earlier
prototype's proof models are a starting point.

## Next milestone: performance

The nucleus favours clarity. Measured on a development JVM (single run,
best of five, not a benchmark):

| Program | Interpreted | Compiled | Clojure |
|---|---|---|---|
| `fib 20` | 218 ms | 155 ms | 0.4 ms |
| `loop` sum to 100,000 | 1.09 s | 6.4 ms | — |

These are cliffs, not constant factors. Known causes:

- **The machine allocates a state map per step** and wraps each step in a
  `try`. A loop iteration costs about 11 µs. The earlier prototype's
  interpreter fused operand evaluation and avoided transient states; those
  lessons need to be ported.
- **Compiled calls to compiled functions go through the machine.** A
  recursive call resolves a late link, finds the installed executable,
  enters a nested machine and binds dynamic vars. Direct calls between
  candidates (with their premises merged) remove this.
- **Step accounting in compiled code** reads a dynamic var per iteration.

The milestone: port the prototype's interpreter and direct-call lessons,
compare against the prototype and SCI on the same programs, and remove the
cliffs without giving up the semantics (worlds, handlers, budgets). The
target is predictable performance: interpretation within a small factor of
other Clojure interpreters, and compiled loops close to Clojure.
