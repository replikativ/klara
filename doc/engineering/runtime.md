# Runtime contracts and boundaries

The implementation is hosted in Clojure on the JVM. This account distinguishes
its working contracts from the broader [objectives](../objectives.md).

## Worlds and definition validity

`klara.world` represents a root as persistent definitions plus version and
reverse-dependency information. A world holds one replaceable reference to a
root. Publication uses compare-and-set; a fork initially shares the pinned
parent root. Root publication is atomic for that world. Settling changes across
several systems is not one multi-root atomic transaction.

`klara.defs` records expansion and value dependencies. CodeIds identify expanded
source under the current canonical profile. Value generations identify actual
definition evaluations: identical source can evaluate to different data through
effects. Early cutoff retains the existing value/generation only when evaluation
is skipped. A pending dependent is refused until its recorded reads hold.

Closures carry captured locals and a basis. World definitions create open
closures; resolving them supplies the executing root. Existing activations and
held closures can retain old definitions while another world evolves. Raising
a basis is explicit. Regression sources include `world_test`, `x1_test`,
`r4_test`, `validity_test` and `staged_compile_test` under `test/klara/`.

Code identity preserves quoted numeric representations and alpha-normalized
syntax scopes. Ordinary metadata and arbitrary identity-sensitive host values
remain outside a universal adequacy claim. See `code_identity_test.clj` and
`syntax_test.clj` for concrete observations and counterexamples.

## Live authority and effects

Persistent definition roots are distinct from the live authority store.
Retaining a root does not preserve or duplicate a consumed token's permission.
`klara.authority` implements resource/evidence/budget/randomness rules, branch
settlement and checked use. T0 frames enforce the corresponding scope and
resumption protocols; [RFC 0001](../../rfc/0001-forks-and-authority.md) states
the intended obligations.

The authority tests cover duplicate use through aliases and collections,
lookup after capture, second resumption, branch settlement and cancellation,
budget/evidence conservation, deferred effects and competing host threads.
These are implementation tests, not a complete authority-store theorem.

Known irreversible operations can be deferred until adoption. Arbitrary Java
mutation and host atoms do not become rollbackable because execution uses a
world fork. Hosted branchable-atom translation, general compensation, portable
adoption receipts and recovery of incomplete settlement remain open. Failed
multi-system settlement can leave an explicit incomplete state rather than
pretending every external change was rolled back.

A world fork is not itself a parallel scheduler. The speculative-pipelining
prototype supplies an explicit worker adapter and admits a narrower effect-free
region; its start/await operations are experimental services.

## Syntax and staging

`klara.syntax` and `klara.expand` implement syntax values, scope identity,
tracked local expansion, definition contexts, grammars and reusable syntax
classes. `syntax_test.clj` checks hygiene, scope lifetime and located failures.
General semantic language descriptors remain proposed in RFC 0006.

Staged Code is a separate representation. `code` constructs syntax, `esc`
splices and `run` executes closed code. Generated binder names are checked for
scope lifetime. `lift` conservatively rejects resource-holding/control values;
it is not an authority-transfer operation. Let insertion and recursive code
builders extend the operational interpreter, with limits documented in the
[staging guide](../guide/05-staging.md).

The [formal specification](../../spec/README.md) covers a smaller staged
calculus. Its executable comparison with T0 has 65 agreements and four declared
differences over 69 corpus programs. The [interpreter guide](../interpreters.md)
explains the translator, observation boundary and remaining equivalence gap.

## Calls, guards and recovery

`klara.stage` admits cached executables under argument, capture, static-value,
world and handler conditions. Fusion dependency guards bind value generations
and source CodeIds separately. Cache validity is root-specific; edits need not
evict code still valid for older worlds.

The compiler has direct-call paths, explicit call context and selected
mid-body numeric deoptimization with source frame reconstruction. Tests cover
resuming at the guard without replaying earlier effects. This does not establish
general native handler capture, arbitrary continuation reconstruction or
recovery of an interior private buffer. The composed private-memory examples
use entry fallback before their candidate effects.

## Deployment

`klara.deploy` stores supported source/Core/immutable data and restores it in a
compatible fresh JVM with an empty cache. Stored data initializers are not
replayed. Numeric classes, metadata and logical container sharing are preserved
within its admitted graph format. Direct open top-level functions can be
reconstructed; captured/pinned closures, live authority, continuations and
opaque mutable objects decline.

This is not a durable arbitrary heap image or a Datahike/Geschichte adapter.
Directory fsync and a general power-loss recovery protocol are not supplied.
`deploy_test.clj` includes fresh-process restore and rejection cases. General
checkpointing must additionally account for live rights and external effects.
