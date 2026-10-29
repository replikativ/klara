# Contributing and discussion

Klara's language design and implementation are open for discussion and feedback.
Start with
[README](README.md), [status](STATUS.md), and
[checked specialization](doc/checked-specialization.md). Historical milestone
reports document their own snapshots; they are not promises about current
coverage.

## Useful questions

- Which programs make persistent worlds and staged optimization useful together?
- How should facts, observations and proof obligations compose across numerical,
  stream and representation transformations?
- Which analyses or cost models justify their expense in a running application?
- Which objectives and accounting rules let components coordinate investments
  without overspending shared CPU, memory or service budgets?
- Where do guards, materialization, world retention or host calls dominate cost?
- Which deployment and resumable-checkpoint boundaries are useful and precise?

Concrete examples and minimized counterexamples are particularly helpful. For
performance reports include the source revision, JDK, inputs, warmup, process
count and complete costs. Keep losing cases and preparation/guard costs visible.
For correctness claims distinguish kernel-checked statements, trusted bridges,
implementation tests and proposed work.

## Work locally

Use a persistent Clojure REPL for implementation/proof iterations. The standalone
suite is `clojure -M:test`; the specialization/proof suite is
`clojure -M:verify`. Check a fresh JVM at integration boundaries. The optional
Wandler oracle and spec/T0 differential runs have separate dependency/fixture
requirements described in [the artifact guide](doc/artifact.md).

Changes to language observations, world validity, authority, admission or storage
need explicit regression cases. Documentation-only edits need not add tests.
Avoid a numerical backend or a new evidence abstraction when an existing shared
path covers the same contract.

Generated verification output belongs under `target/`. Historical measurements
remain with their source identities and reproduction instructions. Do not add
paper build products, downloaded literature, local databases or environment
configuration to the source tree. Source-backed examples and the tests behind
them should remain easy to find and run.

Keep raw review prompts, exploratory discussion and manuscript preparation in
the gitignored `.internal/` folder. Public guides should describe current
contracts and link to tracked tests, proofs or measurements. A reproducible
source snapshot needs frozen identities; a mutable development branch is not
an immutable archive.
