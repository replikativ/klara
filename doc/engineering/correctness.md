# Correctness evidence and open obligations

The prototype combines model proofs, checked candidate admission, regression
tests and trusted implementation bridges. These support different statements.
The [specialization guide](../checked-specialization.md) describes the running
path; this document is its evidence ledger.

## Formal semantics and implementation

The ansatz definitions in `spec/src/klara/spec/core.clj` describe a restricted
small-step calculus. `ws.clj` and `props.clj` establish the named scoping,
determinism, progress, preservation and specialization results. Totality of one
step does not establish termination of arbitrary programs.

The handwritten T0 CEK interpreter is larger. The differential corpus compares
normalized observations after translating spec syntax to T0 Core. It has four
explicitly expected differences; it is not a proof of contextual equivalence.
The front end, translation, observation functions and generated JVM execution
are implementation bridges. See [Reading the interpreters](../interpreters.md).

## Model and candidate evidence

The proof modules below live in `experiments/consolidation/` unless indicated.
The verifier reports named goal/proof hashes, kernel acceptance and direct
self-reference checks. The current consolidated report contains 61 named
receipts, including supporting lemmas, not 61 independent correctness results.

| Statement family | Proof/adapter sources | Remaining implementation bridge |
|---|---|---|
| Polynomial/Horner and finite map/fold equalities | `experiments/proof_staging/proof_staging.clj`, `checked_pipeline.clj` | Reification of actual Core, reference evaluation, checked-Long lowering |
| Bounds and intermediate capacity safety | `interval.clj`, `scalar_core.clj` | Actual literal/value decoding, arithmetic representation and T0 execution |
| Finite private-state simulation | `private_state.clj` | Extracting actual Core loops; complete live-authority and native representation correspondence |
| Actual helper/step equations and loop substitution | `helper_bridge.clj`, `source_model.clj`, `proved_accumulator.clj` | Structural decoder and interpretation of source/owned endpoints |
| Numeric/traversal/private-fold composition | `fold_model.clj`, `checked_pipeline.clj` | Strict-fold lowering, Long behavior, array erasure and JVM execution |
| Producer output facts and bound transport | `producer_model.clj`, `producer_consumer.clj` | Producer materialization, runtime subject identity and admission implementation |
| Finite demand and prefix observations | `demand_model.clj`, `demand.clj` | Actual lazy chunking, Core execution and primitive lowering |
| Original scalar constructor syntax and finite indexed drivers | `scalar_core.clj`, `scalar_driver.clj`, `scalar_sum.clj`, `counted_core.clj` | Runtime Core/value encoding and actual loop decoder |
| Restricted scalar CEK and finite environments | `scalar_cek.clj`, `scalar_finite.clj` | Full T0 simulation, runtime representations and native execution |

Imported ansatz Init statements are loaded in TRUST mode for the optimization
models. Newly constructed proof terms are strictly checked in their captured
environments. This does not independently verify every imported declaration,
the JVM code generator or the complete compiler. Full independent Lean export
and replay of Klara's proof closure remain open.

Per-source witnesses bind actual syntax, interfaces, bounds and endpoints.
Mutating the source or replacing a proof with an unrelated accepted theorem
must fail admission. Equality is composed only at the exact intermediate;
different observations or outstanding obligations cannot silently be merged.

## Observation and failure contracts

Mathematical equality, private-state simulation, input admission and cost
prediction are separate contracts. Profiles do not prove invariants. A proof
about Nat values does not establish checked-Long behavior or effect ordering.
Annotations used as checked claims may fail as declared assertions; optimization
hints require generic fallback when their conditions do not hold. Approximate
statistical replacement contracts remain proposed in RFC 0003.

The private fragment observes admitted values, selected error categories,
outside persistent state and declared dependency behavior. It hides private
administration, allocation and timing. It does not prove contextual equivalence
for arbitrary host object identity, handlers or continuations.

`compile.infer-affine/execute-owned` is the owned intermediate's reference
adapter. It uses a fresh store and finally cleanup on success and failure.
Bare execution of the converted term is not that protocol. Tests check settled
local tokens, cleared payloads and an unchanged caller store. Native array
execution does not mint those local authority tokens. The model's release
theorem is not a theorem about every transition in `authority.clj`.

## Counterexamples and rejections to preserve

- **Overflow motion:** reassociation can turn an overflowing intermediate into
  a mathematical zero. A final-result bound alone does not justify that move.
- **Retained snapshots:** a source value retaining 0 must not later observe 1
  through an incorrectly shared mutable cell. Affine conversion needs retention
  evidence, not merely evidence that a helper performs no writes.
- **Snapshot updates:** every RHS reads the old accumulator before any store.
  Sequentially mutating one slot before evaluating another RHS changes meaning.
- **Lazy demand:** an overflowing element beyond a requested prefix can still
  be forced by Clojure chunking. Moving or suppressing it requires the declared
  totality/observation premise. Zero demand does not erase producer construction.
- **Numeric representation:** equal Long and BigInt values have different
  overflow behavior. Core identity and input layouts must retain that distinction.
- **Wrong dependencies:** stale generations, missing summaries, changed world
  roots, active handlers and unrelated input facts cannot discharge admission.
- **Wrong equations:** ownership-valid code can compute the wrong update.
  Checking ownership alone does not establish semantic preservation.

Regression fixtures are in `experiments/consolidation/cases.edn`, the
corresponding `*_test.clj` files and `test/klara/`. Historical losing timings
remain available through [the performance index](performance.md).

## Composition and the next correctness gate

A staged generator must preserve the reference computation under its declared
observations: running a generated residual on the dynamic inputs must agree
with running the reference on both static and dynamic inputs. Scope safety and
termination alone do not prove that equation. For a stage-polymorphic evaluator,
using one evaluator implementation in present and residual modes still needs
an interpretation relation between those modes, environments and generated
binders. These are separate generator obligations, not consequences of sharing
source code or checking one mathematical identity.

The shared analysis tracks a bounded first-order scalar/layout/retention
domain. Known helper bodies can be summarized and normalized with ordered
argument bindings. Actual callers must still pass layout and ownership checks.
Unknown calls, captures, effects and representation changes decline. This is
not a general fixed-point escape analysis or proof that arbitrary specializers
compose automatically.

Producer facts are immutable and subject-bound. They can discharge a matching
consumer input requirement without rescanning. Current world, host and handler
requirements remain separate. Pure batch entry admits once and invokes a fixed
worker without arbitrary callbacks between admission and use. Producer output
is still materialized; general deforestation is not established.

The substantial open proof gate is a compositional simulation connecting
accepted actual Core loops, their scalar/finite-driver semantics and private
representation invariant to the shared native emitter. Restricted CEK and
finite-environment results supply pieces, not that complete chain. Other open
obligations include general scope freshness, full authority-store soundness,
interior owned recovery and arbitrary lazy/async compilation.

Operational suspension tests hold a T0 continuation between completed native
calls. They demonstrate pinned-world behavior and live cancellation rights;
they do not prove compiled asynchronous capture or durable continuation restore.

## Reproduce

```sh
clojure -M:test
clojure -M:verify
```

The optional spec and Wandler cohorts have separate dependencies, documented
in [Reproduction](../artifact.md). Tests and theorem-receipt counts overlap;
do not sum them as independent evidence. Publication of a new policy does not
prove it equivalent to an older policy; its accepted residuals must separately
satisfy their reference contracts.
