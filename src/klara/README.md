# Host implementation

The parts of Klara written in Clojure, by layer. Guest code (Klara written in
Klara) is in [`lib/klara/`](../../lib/klara/).

| File | Layer | Responsibility |
|---|---|---|
| `lang/term.clj` | L0 | Core terms: constructors, free locals, renaming, substitution, printing |
| `lang/builtins.clj` | L0 | Registry of runtime-provided guest names; trusted host function tables |
| `lang/surface.clj` | L0 | Clojure forms as host macros (`vswap!`, `defrecord`, ...) |
| `lang/expand.clj` | L0, L2 | Clojure surface forms to Core; name resolution; stage levels |
| `runtime/value.clj` | L0 | Closures, continuations, Code, worlds as values |
| `runtime/prims.clj` | L0, L4 | Host primitives where Clojure disagrees with the spec; `same?` |
| `runtime/machine.clj` | L0, L2, L3 | The CEK machine: evaluation, code construction, effect handlers |
| `runtime/prepare.clj` | L0, L4 | Terms prepared into nodes with slot environments and inline caches; profiles recorded in them |
| `runtime/profile.clj` | L4 | Profiles as data: snapshots, annotated references, saved profiles |
| `runtime/world.clj` | L1 | Worlds: definitions, deltas, footprints, slices |
| `runtime/session.clj` | L1 | The session cell, publication, default handlers, module loading |
| `runtime/intrinsics.clj` | L1, L2, L3 | `klara.world`, `klara.stage`, `klara.effect`, `klara.code`, effectful `klara.core` |
| `runtime/job.clj` | L3 | Jobs: fork, budgets, intents, adopt, resume |
| `compile/check.clj` | L4 | The trusted checker: definitional equivalence with premises |
| `compile/own.clj` | L4 | The ownership judgment and erasure check (L4.check.in-place) |
| `compile/facts.clj` | L4 | Effect classes and purity (L4.facts.effect, L4.facts.pure) |
| `compile/anf.clj` | L4 | A-normal form for lowering, so every leave point has a frame state |
| `compile/lower.clj` | L4 | The backend: checked Core to JVM functions |
| `compile/kernel.clj` | L4 | Preparation as a job, candidates, executables, installation |
| `host/api.clj` | — | Driving Klara from Clojure |
| `host/main.clj` | — | Command line: run, repl |
| `host/precompile.clj` | L5 | Precompilation from saved profiles (L4.profile.saved) |

## Trusted base

What must be correct for Klara's guarantees to hold: the machine
(`machine.clj`, `prepare.clj`, `intrinsics.clj`, `job.clj`, `world.clj`,
`session.clj`), the checker (`check.clj`), the ownership judgment
(`own.clj`), the facts (`facts.clj`), the kernel (`kernel.clj`), the backend
(`anf.clj`, `lower.clj`: trusted and tested differentially, not proved), the
Clojure compiler and the JVM. Recipes, specializers, rules, policies and the
guest compiler API (`lib/`) are outside it: their output is checked.
