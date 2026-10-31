# Working in this repository

Guidance for coding agents and new contributors.

## Orientation

1. [design/00-model.md](design/00-model.md): the six nouns (Value, World,
   Code, Continuation, Job, Candidate) and the layers L0 to L5.
2. [spec/](spec/README.md): the rules. Each has an ID like `L3.job.adopt`.
3. [src/klara/README.md](src/klara/README.md): which file implements which
   layer.

## Rule IDs are the index

Every behaviour is named by a rule ID. To understand or change a behaviour:

```sh
grep -rn "L2.run.closed" spec src lib test
```

finds its specification, implementation, conformance case and tests. When you
add behaviour, add or change the rule in `spec/` first, cite the ID in a
comment at the implementation and in a test or a `spec/cases/` file. The
traceability test fails if a raised rule is not specified or a specified rule
is not tested.

## Layers and dependencies

| Layer | Host code | Guest code |
|---|---|---|
| L0 Core | `src/klara/lang/`, `runtime/machine.clj`, `runtime/value.clj` | |
| L1 Worlds | `runtime/world.clj`, `runtime/session.clj` | |
| L2 Staging | `runtime/machine.clj` (code construction), `runtime/intrinsics.clj` | |
| L3 Effects and jobs | `runtime/machine.clj` (handlers), `runtime/job.clj` | |
| L4 Compilation | `src/klara/compile/` | `lib/klara/compiler.clj` |
| L5 Guest compiler | | `lib/klara/compiler/recipes.clj` |

A lower layer never requires a higher one. Higher layers extend lower ones
through the hooks in `machine.clj` (`resolve-hook`, `IExecutable`).

## Working loop

- Start a REPL with `clojure -M:dev -m nrepl.cmdline --port 7999` and use
  `klara.host.api` (`session`, `eval-string`, `load-file`).
- Run the conformance cases: `(clojure.test/run-tests 'klara.conformance-test)`.
- Before committing: `clojure -M:test` in a fresh JVM. It includes the
  lifetime tests, which need the JVM options in `deps.edn`.

## Conventions

- Errors are `ex-info` with `:rule`, `:message` and, where useful, `:hint`.
  Outcomes that callers should handle (jobs, preparation) are maps with
  `:status`, not exceptions.
- Comments explain why. Keep them short.
- New Klara-level functionality belongs in `lib/` as Klara code when it does
  not need machine access; host intrinsics are for what Klara code cannot
  express.
- Do not add a feature without saying how it interacts with worlds, jobs and
  lifetimes ([design/01-lifetimes.md](design/01-lifetimes.md)).
