# Preparation attribution and checked analysis artifacts

Implemented 2026-10-30, following the
[performance account](performance.md). The first change targets
duplicate private analysis rather than introducing a validation-result cache.
The accepted program family, runtime guards and emitted backend remain the same.

## Produce once, check the artifact

Previously, private planning ran the complete producer twice and compared its
results. That detects instability; it is not an independent equivalence proof.
Each pass normalizes and indexes the loop, infers its owned representation,
constructs the enclosing consumer, and creates an ownership derivation.

The default path now constructs one immutable, candidate-local analysis artifact,
then checks it before issuing the existing opaque Endpoint:

```text
named reference function
  → one functional-to-owned inference
  → analysis artifact
  → source/consumer/guard/ownership check
  → opaque accepted endpoint
  → existing erasure, executable validation and publication
```

The artifact is internal production data, not a guest-supplied proof or a cached
validation verdict. `check-analysis!` checks:

- The exact input source object and reconstructed indexed loop source.
- The inferred source identity, function interface and owned loop placement.
- The exact indexed consumer and its binding to the loop result and parameters.
- An independently decoded literal initial vector, its length and Long elements.
- The boolean consumer grammar, parameter layouts, mandatory guards and evidence
  classification; metadata cannot claim a kernel proof.
- The complete ownership derivation, using `affine/verify!` on the actual target.

Functional-to-owned inference remains a trusted/tested bridge. Checking its source
binding and enclosing wiring does not prove an arbitrary conversion correct.
The new checker separates composition/admission obligations from production;
the existing model theorems and implementation bridge tests retain their scope.

Later preparation jobs produce and check their own artifacts. The artifact is
not put in a global lookup table, and no operational counter or mutable profile
is retained in an endpoint. Existing erasure verification, common original-source
reconstruction and checker-registry receipt validation still run. A changed
erasure helper is not hidden behind a reused verdict; an unrelated checker
registration still stales an existing publication receipt.

The diagnostic option `:repeat-private-analysis? true` adds the previous repeated
production while retaining the same new checker. This is a cost control, not a
way to bypass checking. It is supported on explicit baseline strategy requests;
ordinary requests use single production. Both modes emit and admit the same
kind of candidate under the same observation projection.

## Phase attribution

`klara.compile.diagnostics/capture` is an optional trusted-host diagnostic:

```clojure
(diagnostics/capture
  #(let [candidate (staged/prepare root source
                    {:backend :baseline :strategy 'policy})]
     (staged/prevalidate candidate)))
```

The result contains the ordinary value plus bounded phase events. Phases cover
lazy backend initialization, inference, consumer admission, ownership checking,
artifact verification, erasure, host compilation and original-source relation
checking. Source/owned node counts and charged work/emissions/bytes are recorded
by the study. Timings of nested phases are inclusive and cannot be added together
as disjoint costs. Event status records normal return or an exception, not a
substitute semantic-admission decision.

With diagnostics disabled, phase detail expressions and event accumulation are
skipped. No ordinary function-entry instrumentation was added. Enabled collection
retains at most 512 events and counts dropped events. Failed work is recorded and
still propagates its exception. Counters are operational state outside rollback.

The [preparation experiment](../../experiments/baseline/preparation.clj) records
first use with lazy backend loading, separate traced attribution samples, and six
rotating pairs of **uninstrumented** warm preparation/validation/publication.
The control repeats production; it is not a frozen old compiler because both
modes use the new artifact checker. It also records a broad implementation-root
snapshot cost pilot to explain why erasure-verdict caching was deferred. That
pilot is not a complete dependency certificate or an atomic host-state snapshot.

Initial warm REPL attribution put repeated production above repeated erasure
cost. Root-snapshot overhead was not clearly justified for the cheaper erasure
check. The choice here is therefore to retain that check and remove redundant
production. Cold module loading and subsequent function preparation remain
separate costs, both reported. Moving loading outside a timer is not a speedup.

## Checks and remaining campaign

`klara.compile.preparation-test` covers identical endpoints in both modes,
production/check counts, altered source/consumer/layout/derivation artifacts,
later jobs, changed helper invocation, registry receipt invalidation, and bounded
diagnostics including failure. The numerical/overflow and source→residual→owned→JVM
bridge suites exercise the new default path. There are no timing assertions.

Raw process cohorts and reproduction commands are in the
[study report](../../experiments/baseline/preparation-results/README.md).
This closes attribution and one repeated-work item from the review. It does not
complete its preparation agenda: bootstrap initialization, source reconstruction,
host emission, broader validation reuse and retained-artifact accounting remain
targets. Shared entry-premise/dispatch work, actual-syntax correspondence proofs
and the bounded investment demonstration follow in the agreed order.
