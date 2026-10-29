# Klara

Klara is an independent programming language for **self-organizing and
self-optimizing systems**. It is the unifying language project for replikativ's
work on persistent data, versioned state, inference, staged compilation and
proof-guided transformation.

Code lives in versioned worlds. A computation can retain its old world while
another branch changes definitions or an optimizer. Staged programs construct
specialized code; a separate admission boundary checks a candidate's evidence,
input assumptions and dependencies before installing it.

The goal is a running system that can inspect its own operation, learn where
improvement is worthwhile, explore changes in isolated worlds and admit them
under explicit contracts. Operation, resource accounting and investment policy
belong to that same programming model: compiling, proving, training or starting
speculative work should be decisions the application can budget and evaluate.

The current implementation is a research prototype using Clojure syntax on the
JVM. Its language coverage, compiler and proofs are deliberately restricted;
the wider replikativ storage integrations remain planned. Start with the
runnable examples and the
[status and proof boundaries](STATUS.md). The [design objectives](doc/objectives.md)
describe durable development worlds, Clojure compatibility, agent-assisted
evolution and eventual self-hosting across JVM, JavaScript and native targets.

## Run it

Install the Clojure CLI and a JDK; development and native-emission tests use
JDK 25. Dependencies are pinned and fetched on the first run.

```sh
clojure -M:repl       # interactive Klara REPL; :repl/help lists commands
clojure -M:test       # standalone tests and executable documentation
clojure -M:verify     # specialization examples, rejection cases and proof receipts
```

The ordinary tests and verification do not require sibling checkouts.
Klara does not use Wandler at runtime; it provides an optional comparison with
a separate fusion implementation through `clojure -M:test-integration`.
See [reproduction instructions](doc/artifact.md) for its fixture requirements.

In the Klara REPL:

```clojure
(defn square [x] (* x x))
(square 7)
;; => 49
```

Continue with the [language guide](doc/guide/README.md) or
[checked specialization](doc/checked-specialization.md), which follows source
code through preparation, validation, publication and runtime admission.

## What to explore

- **Worlds and effects:** immutable definition roots, pinned execution, explicit
  basis changes, scoped forks and live authority.
- **Staging:** `code`, `esc`, `run`, let insertion and ordinary code builders.
- **Syntax:** syntax objects, tracked local expansion and reusable grammars.
- **Programmable optimization:** numerical rewriting, fusion and private
  accumulation through one compiler path; a source-backed guest planner can
  choose and evolve optimization policy.
- **Speculative pipelining:** an outcome predictor trains online and overlaps
  a checked follow-up with its producer; [the example](examples/staging/16-learned-speculation.md)
  covers hits, misses, isolation and costs.
- **Accounting and investment:** explicit budgets, measured preparation costs
  and a bounded planning policy; learned profitability and broader resource
  metering are development objectives.
- **Correctness:** kernel-checked results for named restricted models, actual
  endpoint checks and differential tests for the remaining runtime bridges.
- **Deployment:** restricted source/Core/data bundles that restore in a fresh
  JVM. This is separate from arbitrary continuation or heap checkpointing.

Useful entry points:

| Path | Purpose |
|---|---|
| [Guide](doc/guide/README.md) | Learn the language through tested transcripts |
| [Examples](examples/README.md) | Staging, worlds, inference and specialization |
| [Objectives](doc/objectives.md) | Persistent development, source/deployment, compatibility and self-hosting goals |
| [Checked specialization](doc/checked-specialization.md) | Current compiler lifecycle and evidence boundaries |
| [Reading the interpreters](doc/interpreters.md) | Formal step semantics, the CEK machine and their differential tests |
| [Architecture](doc/architecture.md) | Implemented components and longer-term design |
| [Contributing](CONTRIBUTING.md) | Discussion topics, development and verification |
| [Artifact guide](doc/artifact.md) | Reproduce results and prepare a frozen artifact |
| [RFCs](rfc/README.md) | Design proposals and their implemented subsets |
| [Compiler notebook](notebooks/compiler_walkthrough.clj) | Optional Clay walkthrough of the hosted compiler passes |
| [Engineering evidence](doc/engineering/README.md) | Runtime contracts, proof boundaries, measurements and limitations |

The public discussion should help sharpen the programming model and its
implementation. We particularly welcome concrete programs, counterexamples,
analysis/optimization composition examples and measurements that expose costs.
See [Contributing](CONTRIBUTING.md) for the current questions.

Licensed under [Apache-2.0](LICENSE). Klara uses Clojure as a dependency and
[ansatz](https://github.com/replikativ/ansatz) for proof construction/checking.
