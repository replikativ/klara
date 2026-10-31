# Host implementation

The parts of Klara written in Clojure, by layer. Guest code (Klara written in
Klara) is in [`lib/klara/`](../../lib/klara/).

| File | Layer | Responsibility |
|---|---|---|
| `lang/term.clj` | L0 | Core terms: constructors, free locals, renaming, substitution, printing |
| `lang/builtins.clj` | L0 | Registry of runtime-provided guest names; trusted host function tables |
| `lang/expand.clj` | L0, L2 | Clojure surface forms to Core; name resolution; stage levels |
| `runtime/value.clj` | L0 | Closures, continuations, Code, worlds as values |
| `runtime/machine.clj` | L0, L2, L3 | The CEK machine: evaluation, code construction, effect handlers |
| `runtime/world.clj` | L1 | Worlds: definitions, deltas, footprints, slices |
| `runtime/session.clj` | L1 | The session cell, publication, default handlers, module loading |
| `runtime/intrinsics.clj` | L1, L2, L3 | `klara.world`, `klara.stage`, `klara.effect`, `klara.code`, effectful `klara.core` |
| `runtime/job.clj` | L3 | Jobs: fork, budgets, intents, adopt, resume |
| `compile/check.clj` | L4 | The trusted checker (definitional unfolding) and a normalizing recipe |
| `compile/lower.clj` | L4 | The backend: checked Core to JVM functions |
| `compile/kernel.clj` | L4 | Preparation as a job, candidates, executables, installation |
| `host/api.clj` | — | Driving Klara from Clojure |
| `host/main.clj` | — | Command line: run, repl |

## Trusted base

What must be correct for Klara's guarantees to hold: the machine
(`machine.clj`, `intrinsics.clj`, `job.clj`, `world.clj`, `session.clj`), the
checker (`check.clj` except `normalize`), the backend (`lower.clj`), the
Clojure compiler and the JVM. Recipes, policies and the guest compiler API
are outside it.
