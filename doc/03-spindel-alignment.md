# Klara ↔ spindel alignment (2026-10-27)

Spindel (`../spindel`) is the replikativ reactive runtime: signals, spins,
`track`/`await`, copy-on-write forks, snapshots, rebuild by re-execution,
yggdrasil-backed world forks with affine settlement. Its formalism
(`spindel/docs/engine-formalism.md`) states laws with Holds/Conjectured
status and `file:line` evidence; it is not mechanized. Klara's design
(`01-core-v1.md`, `02-examples.md`, the Codex review) independently arrived
at several of spindel's mechanisms. This note maps the two, records where they
disagree, and proposes how they merge: **spindel as the implementation-level
semantics and runtime, Klara Core as the specification, related by
refinement**.

## 1. Concept map

| Spindel | Klara | Notes |
|---|---|---|
| execution context | world value + basis | a context is a world with an engine attached |
| signal | world cell | |
| spin (`:computation`) | fiber running a demanded computation | |
| spin (`:resource`) | resource sort; a fiber with external effects | formalism marks resource spins non-deterministic (✗ in the summary table) |
| `await` (monad, `engine-formalism.md` §1.2) | `perform` with a one-shot continuation | await-resume = handler resume |
| `track` (comonad, §1.1) | recorded reads in the demanded-computation graph (C §4.3) | the same mechanism as Klara's expansion invalidation (X1) |
| dirty flag + generation guard | dirty marking + lazy re-verification with early cutoff | |
| typed delta algebras (§1.3) | — | Klara has no incremental-delta story yet; see §4 |
| `fork-context` (overlay, parent-following) | — | Klara's `fork` is snapshot (Q4); following is a separately named operation |
| `snapshot-context` / `restore-snapshot` | `fork` (snapshot meaning) | |
| rebuild by re-execution (cached results, continuations rebuilt) | multi-shot resumption by replay | the JVM has no native continuations |
| deterministic spin ids under replay (§1.5) | content/replay identity | needed for replay-based resumption |
| resume idempotence (§1.9) | one-shot safety of continuations | |
| `ygg/register!` systems | branchable sort | |
| `ForkHandle`, affine settlement (#41) | authority token for settle/branch | exactly the Codex fix (authority, not non-copyable objects) |
| `partition-fork!` (#43): disjoint, exhaustive, consumes the parent handle | authority split | the same structure as evidence split (σ): every part exactly once |
| `:advancing` lease, fail-closed settlement, `:incomplete` recovery state | settlement protocol | Klara had none; adopt |
| simulation context with virtual time | a `:time` effect with a virtual-time handler | makes sleep/debounce deterministic under test |
| external side effects not isolated across forks (`forking.md`) | G10: irreversible effects in forks | both systems lack the rule |

## 2. Where they disagree

1. **Default fork semantics.** Spindel's `fork-context` is parent-following on
   shared paths (overlay falls through to the parent's live backend); Klara
   decided snapshot (Q4). The difference is only *what the overlay reads
   through to*: the parent's mutable backend (following) or the parent's root
   value pinned at fork time (snapshot). With persistent state, pinning costs
   nothing. Proposal: Klara `fork` = overlay over the pinned parent root;
   spindel's current behaviour becomes `fork-following`, kept for
   speculative rebase.
2. **Raw `@deref` of a stale spin.** Spindel documents that `@` on a
   stale-clean spin returns the cached value, and that across a fork the
   staleness is permanent (`forking.md`, "Forking with an un-drained
   change"). In Klara reading a demanded computation must re-verify (or be
   a marked REPL-only escape). This is the same hazard as v0's host-namespace
   leak found by X1: a read path that bypasses the dependency graph.
3. **Typed deltas.** Spindel propagates typed deltas (scalar, sequence, map,
   interval algebras) for efficient incremental updates; Klara's invalidation
   only marks dirty and recomputes. Klara should adopt delta algebras for
   world cells (the DBSP-style cross term in the ESOP paper's interaction
   section is the same algebra).
4. **Formalization medium.** Spindel's formalism is prose laws with code
   citations; Klara Core is to be specified in ansatz (X3). Shared
   obligations need shared identifiers now, so a later refinement proof can
   cite both.

## 3. Obligations Klara imports from spindel

| Id | Spindel law | Spindel status | Klara reading |
|---|---|---|---|
| S1 | Glitch-freedom: within one drain a spin re-runs at most once per generation (§1.4) | Holds (sync portion) | demanded computations re-verify at most once per basis change |
| S2 | Deterministic ids under replay (§1.5) | Holds | replay identity for multi-shot by re-execution |
| S3 | B-gate: re-registering a computation spin re-runs iff needed (§1.6) | Holds (conservative) | early cutoff soundness |
| S4 | Per-observer delta-once delivery (§1.7) | Holds, with a conjectured latent issue | no double counting of world deltas (the evidence discipline for deltas) |
| S5 | Commutativity of independent signal changes (§1.8) | Conjectured | confluence of independent world writes |
| S6 | Resume idempotence (§1.9) | Holds | one-shot continuation safety |
| S7 | Fork cache soundness: the parent's cache is never observed stale by a fork (`forking.md`) | Holds (reactive reads only) | cross-fork cache validity (C O8) |
| S8 | Settlement exactly once; mutually exclusive merge/discard/transfer (#41) | Holds (tests) | authority conservation |
| S9 | Partition is disjoint and exhaustive; consumes the parent authority (#43) | Holds (tests) | authority split is σ |
| S10 | Fail-closed settlement; `:incomplete` after partial durable mutation | Holds (tests) | settlement protocol under failure |

## 4. What each side should take from the other

**Klara takes from spindel:** the affine settlement and partitioning model as
its authority invariant (replacing the dynamic-tag approach the Codex review
rejected); replay-based multi-shot resumption; virtual time as a handler;
typed delta algebras for world cells; the law-with-evidence formalism style.

**Spindel takes from Klara:** snapshot as the default fork meaning (pinned
parent root); recorded *code* dependencies (definition and syntax-extension
changes as tracked reads, from X1), so hot code changes invalidate spins
precisely; receipts for adopted results; the reversible/irreversible effect
classification with deferred intents for external effects inside forks (G10).

## 5. Merge path

| Phase | What | Risk control |
|---|---|---|
| P0 (now) | this map; shared obligation ids S1–S10 in both formalisms | none needed |
| P1 | Klara v2 design adopts spindel's authority/settlement model, replay resumption, virtual time; decides the snapshot-vs-following default together with spindel | spindel API unchanged |
| P2 | **X6**: implement Klara's `:expand`/`:analyze` nodes as spindel computation spins (syntax extensions and definitions as signals), replacing X1's bespoke graph in v0; compare correctness on X1's tests and cost on its benchmark | if spindel cannot express basis pinning or code dependencies cleanly, keep the graphs separate and record why |
| P3 | spindel becomes Klara's runtime layer on JVM and JS (fibers, forks, tracking, settlement); spindel's formalism is stated as a refinement of Klara Core for the fragment {cells, demanded computations, await, fork, settle}; the shared fragment is mechanized in ansatz | spindel stays independently releasable for Simmis; Klara depends on spindel, not the reverse |

**Refinement statement (P3 target).** For programs in the fragment, every
observation of the spindel engine (values delivered to awaiting fibers,
contents of settled branches) is an observation of Klara Core under the
reference handlers, except for the documented escapes: raw `@deref`,
`fork-following`, and unclassified external effects.

**The open question for Christian:** should spindel's default fork become
snapshot (pinned parent root), with parent-following renamed, or does
Simmis rely on parent-following in ways that make that change costly?

## 6. sci: the second existing implementation (added 2026-10-27)

`../sci` (branch history since 2026-08) has an opt-in forkable runtime
(`sci/doc/forking.md`, `sci/doc/fork-state-audit.md`): world snapshots,
namespace and Var control state isolated per fork, fork-local SCI delays,
JVM promises and `memoize` caches, managed mutable `deftype` fields across
forks, rejection of affine host resources (atoms, refs, agents, volatiles,
transients, lazy seqs, pending tasks, mutable Java collections) unless an
explicit `:fork-fn` policy handles them, shallow copies of host arrays with
aliases preserved, and forkable continuation contexts
(`sci/capture-continuation-context`, `retarget-continuation-context`).

Consequences for Klara:

1. **Hosted mode (L1) can start as forkable sci plus Klara's expander**, long
   before Klara's own compiler. This is ring 6 of `doc/bootstrap.md` (an
   interpreter as the universal seed) arriving first instead of last.
2. **sci's fork-state audit is the most complete list of the seams in
   `02-examples.md`** (G6 deep value-ness, G7 laziness, binding conveyance,
   mutable fields): Klara should adopt its classification table rather than
   re-derive it.
3. **Laziness**: sci rejects direct host lazy seqs at forks because their
   realization cache is a small continuation and bodies may have effects; it
   files managed lazy continuations under the future fiber model. Klara's
   refinement (research note F): pure lazy seqs are values (their memo is
   idempotent), effectful ones are resources, and laziness in general becomes
   a `yield` effect with a handler, which is the fiber model sci points to.
4. **Two implementations, one specification**: spindel (reactive engine, world
   settlement) and sci (interpreter with Clojure semantics under forks) both
   refine Klara Core for overlapping fragments. Shared obligation ids (S1–S10
   plus sci's audit rows) let the conformance corpus test both.
