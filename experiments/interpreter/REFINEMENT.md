# Bounded execution and emission refinement

This experiment connects a small emitted representation to the existing scalar
proofs, and strengthens executable checks for private storage and recovery.
It adds no production execution tier. The reference CEK remains the behavioral
oracle for implementation checks; the scalar CEK is a smaller proof model.

## A source-specific checked lowering

[`scalar_block.clj`](../../verification/consolidation/scalar_block.clj) lowers the already
admitted scalar fragment: scoped locals, nonnegative Long literals, sequential
`let`, and exact binary `+`/`*`. Every instruction writes a fresh slot. Reads
must refer to initialized slots; operands execute left to right. There is no
slot reuse, reassociation, dead-code elimination, looping or closure conversion.

For example, a one-argument body `(+ x 3)` becomes:

```clojure
{:arity 1
 :instructions [[:copy 1 0] [:literal 2 3] [:add 3 1 2]]
 :result 3 :next 4}
```

Initial slots use de Bruijn order, so slot zero denotes the most recent input.
The model uses a functional slot store, natural-number values and an explicit
capacity. Each read/literal/arithmetic operation performs its declared capacity
check; failure stops the block. It does not silently continue with a default.

For each actual source/block pair, the checker constructs a proof of:

```text
forall rho cap,
  slotRun(encodedBlock, rho, cap) = scalarChecked(encodedSource, rho, cap)
```

The result is `Option Nat`: either an exact answer or the modeled overflow
failure. Both successful and overflowing executions are covered. Proof tactics
are untrusted generators; the resulting term must pass the ansatz kernel in
the captured model environment. An incomplete proof declines. The bounded
simplification strategy need not succeed for every valid block.

This observation excludes allocation, elapsed time, instruction metering and
interrupt timing. A compiled backedge budget needs a separately stated contract;
native instruction counts cannot silently replace reference CEK fuel.

Per-source proof jobs run from the captured immutable model environment without
installing declarations into the global ansatz session. A test checks this with
an unrelated global environment. Initial model construction still uses the
existing hosted ansatz REPL bootstrap; it is not a guest-world compiler service.
For hot-path use, a generic lowering theorem with cheap instantiation would
avoid repeatedly running this symbolic proof search. Its cost is not assumed
negligible, and compilation/proof investment needs its own policy.

The generic `slot-block-cek` theorem composes that receipt with the existing
scalar CEK transition/meaning and termination-budget results. Its conclusion
says the scalar CEK reaches a final state and its observation equals the block
result. This is composition at the exact source and target endpoints.

This is **per-source translation validation**, not a proof that the lowering
function is correct for all syntax. Receipts bind the actual source CodeID,
arity, block, goal and proof hashes. Verification reconstructs both refinement
and composed execution goals. Wrong operators, stale sources, invalid slot
reads, unrelated proofs and erased overflowing intermediates are rejected.

## Hosted emission bridge

`emit-long` maps a validated block to a small Clojure `fn` with ordered local
bindings. Clojure compiles it to JVM bytecode; this experiment does not generate
bytecode directly. Its entry checks exact nonnegative Long inputs, arity and
anchored primitive identities. Arithmetic uses checked `+` and `*`, with
unchecked compilation disabled. The capacity is `Long/MAX_VALUE`.

The bridge supports at most 20 inputs and rejects other layouts rather than
providing generic fallback. It has no interior suspension/reconstruction and
executes only a closed scalar block with no guest callbacks or effects.
This is an inspectable correctness experiment, not a measured fast tier or a
replacement for the existing compiler. The wrapper still uses hosted calling
conventions; no performance claim is made for it.

The Core decoder, runtime input ordering, numeric representation, Clojure form
emission and host compiler/runtime remain implementation bridges. In
particular, a Nat theorem alone does not prove actual JVM overflow behavior.
Differential tests check those bridges for the selected examples and errors.
As in the existing scalar models, imported ansatz Init declarations are loaded
in TRUST mode; new proof terms are checked in that environment. Independent
Lean export/replay of the proof closure remains separate work.

## Storage, snapshots and recovery

[`refinement_checks.clj`](refinement_checks.clj) extends the existing bridge and
activation checks with two obligations:

- **Writable storage separation.** Enumerate active registers, local/slot
  arrays, frame containers, frame arrays, operand buffers and activation
  scratch buffers. Original execution and two thaws must share none of them.
  Advancing one thaw must leave the other and reusable snapshot observations
  unchanged. Immutable plans and sealed closure captures may be shared.
- **Failure and recovery order.** At every pause before selected arithmetic
  failures, transfer a thaw to each T0 driver and compare the outcome. Overflow
  before division by zero differs from division by zero before overflow.
  Unselected failing branches stay unselected. A failed private execution
  loses its controller lease and cannot subsequently be frozen or resumed.

These are executable bounded checks, not universal ownership/simulation
theorems. Existing trajectory checks compare each private pause with a reachable
reference configuration, preserving closure aliases, recursive captures,
source metadata, pinned basis and entry decimal context. They bound the search
for corresponding transitions; they do not prove progress for arbitrary code.

## What remains across the five correctness boundaries

| Boundary | Current evidence | Remaining task |
|---|---|---|
| Execution refinement | Per-source scalar block proofs; concrete private/T0 trajectory checks | General concrete-machine simulation, including calls and loops |
| Snapshot correctness | Independent writable storage and resumption checks | Universal freeze/thaw relation and complete reachable-store ownership |
| Worlds and authority | Pinned-basis/capture checks; unsupported resource construction rejected | Mixed-world closures, canonical cross-tier identity and authority simulation |
| Compiled regions | Scalar block receipts and tested hosted emission; existing checked compiler contracts | Emitter correspondence and declared recoverable points for larger regions |
| Effects | Pure admission rejects host calls, handlers, staging and mutable host inputs | Explicit supported effect/capability model and exactly-once recovery |

The [counted-loop extension](COUNTED-LOOP.md) now implements the next bounded
slice: simultaneous argument evaluation, checked step composition, explicit
backedge snapshots, and generic/primitive emission. General host calls and
arbitrary native-stack capture remain outside that fragment.

## Reproduce

```sh
clojure -M:runtime-refinement
```

The command runs the scalar block tests and private node/bridge/activation
checks, and writes a source-hashed report to
`target/runtime-refinement/report.edn`. REPL iteration can require
`consolidation.scalar-block` and invoke `lower`, `certify`, `verify?` and
`emit-long` directly. Reloading the small proof module is safe; do not reload
the private kernel `deftype` definitions beneath live experimental objects.
