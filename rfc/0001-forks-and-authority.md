# RFC 0001: Forks and authority

- Status: draft
- Owner(s): Christian Weilbach
- Experiments: X1 (v0), spindel #41/#43 (affine settlement, partition), sci forking runtime, W4/W5 (planned)
- Obligations: AU1–AU7 below

## Motivation

Klara's central workflow forks a running world, works in the branch, and
adopts or discards the result (`02-examples.md` E2, E6). Two first attempts at
making this safe failed:

- "Only values fork; resources are non-copyable, checked by dynamic tags" —
  `(let [r (open "f")] [r r])` duplicates a resource without any copy
  operation, a persistent map may contain an array, and a closure can reach a
  resource through `resolve` (Codex review §1).
- "Fork = copy everything copyable" — weights must be split, not copied;
  resampling conserves mass only across the population; external effects (an
  email sent in a branch) cannot be undone (G1, G10).

## Proposal

1. **Data is aliasable; authority is not.** Any value may be referenced many
   times. What cannot be duplicated is an *authority* — a capability to
   consume a resource, branch or settle a branchable system, spend evidence,
   spend budget, or draw randomness. Authorities are tokens with the
   lifecycle open → advancing → settled | incomplete (spindel's `ForkHandle`).
2. **Fork** takes a snapshot of the world (an overlay over the parent root
   pinned at fork time) and splits every authority the forked computation
   holds, per kind:

   | Authority | Split at fork |
   |---|---|
   | resource | none (transfer only; a fork needing it in both branches is rejected) |
   | branchable system | `branch!` per branch; settlement authority partitioned (disjoint, exhaustive) |
   | evidence | mass-preserving split; populations use join-then-split |
   | budget | split; hard components (memory, deadlines) cannot be overspent |
   | randomness | key split; shared only under `:coupled` |

3. **Effects are reversible or irreversible.** Effects on branchable systems
   inside a branch are reversible. Irreversible effects (host I/O) are
   deferred as intents, executed on adoption and dropped on discard; acting
   directly requires an explicit capability recorded in the receipt.
4. **Settlement** of each authority happens exactly once, fails closed, and
   leaves `:incomplete` after a partial durable mutation for explicit
   recovery.
5. **Results.** `fork` returns branch results as values; unadopted branches
   are discarded at scope exit; `adopt!` hands a branch to the adoption
   boundary (e.g. Simmis review) with its receipts.
6. **Following** (`fork-following`, spindel's overlay over the live parent) is
   a separate operation. It is well-defined where branch and parent write
   disjoint paths (zero interaction in the ESOP paper's sense) and resolves
   conflicts by shadowing (last-writer arbitration) otherwise.

## Alternatives considered

- **Affine objects checked dynamically** (v1): unenforceable without tracking
  every alias; rejected (Codex §1).
- **Static affine types for all code** (Rust, metacarp): contradicts the
  untyped core and features à la carte; kept as the opt-in narrowing layer
  that erases dynamic authority checks.
- **Parent-following as default** (spindel today): efficient for speculative
  rebase but not a copy in the calculus; kept as a named operation.
- **Capabilities in the style of object-capability languages** (E, Effekt's
  effects as capabilities): the proposal is this, applied to fork authority.

## Obligations and falsifiers

| Id | Obligation | Status | Check / falsifier |
|---|---|---|---|
| AU1 | No program duplicates an authority (dynamic check) | Conj | adversarial suite: duplicate locals, nested collections, metadata, escaping closures, lookup after capture, repeated resume, cancellation (Codex experiment 1) |
| AU2 | Settlement exactly once, fails closed | Holds in spindel (tests) | port spindel's tests to the Klara reference machine |
| AU3 | Partition is disjoint and exhaustive and consumes the parent | Holds in spindel (tests) | same |
| AU4 | Snapshot fork: no parent write after the fork is visible in the branch | Conj | litmus tests on spindel with pinned roots |
| AU5 | Deferred intents execute iff the branch is adopted | Open | trace tests with adopt/discard/cancel |
| AU6 | Evidence mass is conserved across fork/resample/discard | Holds operationally (foerster) | property test over SMC runs |
| AU7 | Static affine layer erases dynamic checks without changing traces | Open | differential test with the layer on/off |

## Compatibility

L0: linked Clojure code holds no Klara authorities; its state is shared across
forks (documented). L1: hosted atoms become branchable cells; Java objects are
resources by default. L2: `fork`, `adopt!`, `branch!`, `:coupled` are new names.

## Open questions

1. Should authority checks be fully dynamic in v1, or should the affine layer
   ship together with them? (Veit: cost of affinity vs forkability in metacarp.)
2. Is "deferred intents" sufficient for irreversible effects, or do some
   workflows need compensation instead (sagas)? (Simmis product experience.)
3. Can Effekt-style capability passing serve as the uniform mechanism for both
   effect handlers and fork authority? (Jonathan Brachthäuser.)
