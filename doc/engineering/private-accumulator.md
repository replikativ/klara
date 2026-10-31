# Enclosed private accumulator preparation

Implemented 2026-10-30. This adds one terminal endpoint to the
[funded preparation strategy](preparation-strategies.md). It composes checked
local-call inlining with the existing ownership converter, retains the original
entry identity, and spends the same job's allowance. The semantic bridges are
tested; this adds no kernel theorem about the implementation.

## Guest program and policy

In a Klara REPL with `examples/compat` as a source root:

```clojure
(require '[klara.private-optimizer])
(def source
  (code
    (fn [n bias limit]
      (let [step (fn [acc i]
                   (assoc (assoc acc 0 (+ (nth acc 0) i))
                          1 (+ (nth acc 1) bias)))]
        (let [acc (loop [i 0 acc [0 0]]
                    (if (< i n)
                      (recur (inc i) (step acc i))
                      acc))]
          (< (+ (nth acc 0) (nth acc 1)) limit))))))
(def kernel (run source))
(def subject (perform :stage/subject source))
(def job (perform :stage/job {}))
(klara.private-optimizer/prepare job subject)
(kernel 5 3 26)
;; => true
```

The module uses `code`, `esc` and `lift` to generate a policy with a fixed number
of inline rounds, then runs that policy as ordinary guest code. Its decisions
are `:local-call` followed by `:private-accumulator`. The second action is
terminal: the controller finishes a source-level rewrite sequence and hands
the accepted region to a representation backend. It does not continue applying
functional recipes to owned IR.

The module requests preparation in a fork and installs after adopting the
result. This is the existing Prepared lifecycle, not a second execution engine.
The inlined helper and its eventual mutable implementation implement the same
original `kernel` entry. There is no need to replace application source with
the inlined residual or call a separately named optimized function.

## Accepted relation

```text
original named function
  -- checked local-call edge --> functional residual
  -- checked enclosed-region edge --> indexed owned Core
  -- tested derivation erasure --> emitted Clojure/JVM implementation
```

The final edge crosses representations and is issued by the trusted endpoint
adapter after production and source/consumer/ownership checking. The
[preparation-cost slice](preparation-costs.md) removes duplicate production;
ownership derivation checking
remains mandatory. Diagnostic receipts describe both edges; opaque capabilities
authorize their acceptance. The baseline executable checker requires the
endpoint capability, connected edges and admission guards. Erasure and native
execution remain trusted/tested bridges rather than mathematically verified
compilation.

The accepted family has at most four Long parameters, one literal nonempty
Long-vector accumulator, scalar loop state, checked snapshot updates and a
pure boolean consumer. The consumer may use fixed in-range `nth`, `count`,
supported scalar primitives, scalar lets and conditionals. Direct vector uses,
dynamic indices, arbitrary calls, metadata/identity observers and escaping
results decline. Broader ownership inference is not implied by this endpoint.

The generated loop uses one fresh private `long[]` per invocation. Update
right-hand sides are evaluated before stores according to the existing checked
update plan. The result is frozen once into a persistent vector for the final
consumer; that allocation is still present. The final externally visible result
is boolean. The temporary, its snapshots and its identity cannot be returned or
passed to arbitrary consumers in this admitted syntax.

This removes the known escaping-vector identity counterexample for this family.
It does not establish full host contextual equivalence for all Klara programs:
the subject contract still reports its experimental status. Allocation failures,
physical memory usage and unrestricted host observation are not newly proved.

Runtime entry guards check Long argument layouts, current primitive roots and
the required exception-handler context. Non-Long inputs fall back to T0.
Input vectors and host buffers are not admitted, so no mutable argument is
assumed to become private merely because profiling saw no alias. Reference
roots and compiler-policy roots remain separate.

## Funding, evidence and checks

Source/owned traversals are bounded and charged to the shared job; conversion
retains the existing bounded analysis. Emitted form bytes and compilation
attempts are charged before host compilation. This is operational sponsorship,
not exact CPU accounting or wall-clock preemption. Later validation can repeat
bounded derivation/erasure checks; it does not run source code or compile a new
class. A discarded or exhausted request retains previous charges.

`klara.compile.private-accumulator-test` covers original entry identity, the
two-edge chain, nonempty array representation evidence, a single funded
emission, zero/negative iteration counts, numerical and overflow behavior,
layout fallback, forged/missing evidence, unsafe consumers, exhausted budgets,
and a real staged guest policy preparing in a fork. Rejection checks run before
emission. Tests compare results/classes and selected failures; they are not a
universal semantic proof.

The [diagnostic experiment](../../experiments/baseline/private_accumulator.clj)
compares T0, generic baseline after inlining, and the composed private endpoint
on the same source and inputs. It records preparation/validation costs and all
samples; it has no timing assertions. Its [raw cohorts](../../experiments/baseline/private-accumulator-results/)
are warm-process diagnostics, not an independent performance evaluation.

Next steps are eliminating final materialization through checked producer/consumer
lowering, broader enclosed-region families, stronger source/owned/JVM
correspondence. [Deterministic candidate selection](candidate-selection.md) and
[enclosed consumer model results](private-accumulator.md#enclosed-consumer-correspondence) now strengthen this
path, while retaining explicit implementation bridges.
No autonomous investment policy or learned predictor is installed by this change.

The [allocation planning agenda](../objectives.md#bounded-allocation-and-reusable-storage) records later capacity
analysis and workspace reuse. This endpoint still allocates per invocation;
scalar replacement and eliminating final materialization precede that broader work.

## Enclosed consumer correspondence

`verification/consolidation/enclosed_consumer.clj` proves four additional results
in Ansatz, independently checked by its kernel:

| Theorem | Statement |
|---|---|
| `private-enclosed-consumer-refines` | The private-state simulation remains valid after a pure boolean observer of its final value |
| `private-enclosed-checked-consumer-refines` | The same result allows a pure consumer to produce either a boolean or a failure category |
| `private-source-failure-precedes-consumer` | A source-region failure is preserved without evaluating the final consumer |
| `private-enclosed-releases` | The modeled safe private region reports its resource released on exit |

The observer receives the final value, not an alias, identity or retained
intermediate version. Failure categories and outside-state observations remain
in the result. The safety premise still has to hold for the region; the theorem
does not infer ownership from past executions. The model is finite scalar
private plans over naturals with an explicit capacity check. It is not a
theorem about JVM GC, arbitrary vector loops, divergence or host observation.

The implementation bridge test generates singleton accumulator loops with a
local update helper. It compares five observations:

```text
finite plan model
  ↔ original Core through T0
  ↔ actual inlined residual through T0
  ↔ actual owned Core through its isolated authority protocol
  ↔ installed JVM implementation under the original entry
```

The cohort covers four seeds including Long maximum boundaries, four iteration
counts, three thresholds, and both plain and checked-increment consumers:
96 input cases. Overflow can occur in the loop or only in the final consumer.
Source/owned/JVM correspondence is exercised through real production adapters;
it is tested, not proved by the abstract model theorem. The existing endpoint
tests separately cover richer two-field updates, unsafe consumers and layout
fallback.


The four goals/proofs are exported by `:verify` with kernel acceptance and
self-reference checks. Core extraction, ownership analysis, checked Long
arithmetic and JVM erasure remain tested bridges; see the
[correctness ledger](correctness.md).
