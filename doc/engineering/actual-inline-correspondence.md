# Actual local-call syntax correspondence

Implemented 2026-10-30. This strengthens the existing
[local-call recipe](guest-local-calls.md) and
[source-relation admission](candidate-selection.md). It adds an independent
check of actual source/residual syntax, two kernel-checked lexical model
results, and richer execution bridges. It does not establish whole-compiler
correctness or a general lambda-calculus substitution theorem.

## The production check

The producer in `compile.local-calls` still checks nonescaping fixed-arity uses,
freshens each helper copy and emits ordered argument lets. The separate
[`compile.inline-check`](../../src/klara/compile/inline_check.clj) decoder checks
unique symbolic binders, arities and lexical scope, then decodes both actual
endpoints to indexed Core. It covers the fixed-arity baseline grammar; staging,
handlers and unsupported control do not silently enter this check.

The checker independently eliminates the selected helper in indexed syntax:

- Removing the helper binding decrements references to outer locals.
- Each argument is evaluated once, in source order. Later argument expressions
  are shifted over the earlier temporary lets, retaining their caller scope.
- The helper body keeps its parameter indices; its free captures are shifted
  over intervening caller binders. Nested binders adjust each cutoff.
- Escaping helper references or mismatched call arities reject.

The expected indexed residual must have the same CodeId as the decoded actual
residual. CodeIds preserve literal numeric representations, unlike Clojure
numeric equality. The checker does not call the producer's `ir/freshen` or use
its named substitution routine. All traversals during production are charged to
the preparation job. This is independent structural checking, not a second
execution of the same named rewrite.

A compact example explains why both shifts matter:

```clojure
(fn [x y]
  (let [h (fn [a b] (+ x (- a b)))]
    (let [x (+ x 10)]
      (h y x))))
```

`h` captures the outer `x`. Its second argument reads the inner `x`, even after
the first temporary argument has been bound. Giving both occurrences the nearest
textual spelling would capture the wrong value. Indexed correspondence checks
these two lexical relationships independently of the generated names.

Each accepted local edge records a `:syntax-correspondence` description with
source/residual IDs and checked call count. Admission in `compile.relation`
recomputes that check for the actual opaque edge endpoints. Guest policies cannot
replace the checker by supplying a diagnostic receipt map. Endpoint ownership,
consumer grammar, runtime guards and registry-sealed publication remain separate
checks; this source relation does not replace them.

## Kernel results and their scope

[`consolidation.indexed-binding`](../../verification/consolidation/indexed_binding.clj)
defines indexed literals, locals, binary combination and single-binding lets,
with arbitrary value type, literal interpretation and total binary operation.
Ansatz strictly kernel-checks:

| Result | Statement |
|---|---|
| `index-lift-agreement` | Environment lookup agreement survives extending both environments with the same bound value and lifting the index renaming |
| `index-renaming-preserves-evaluation` | An arbitrary renaming satisfying lookup agreement preserves evaluation in this expression model, including nested lets |

These supply a lexical invariant for index shifting. They do not prove that the
Clojure decoder implements the model, nor cover general closures, recursion,
checked-Long exceptions or JVM emission. The existing
[ordered-call theorem](recipe-composition.md) separately models ordered arguments,
state and failure short-circuiting. Combining those model statements is not yet
an end-to-end theorem about the full actual inliner. Imported proof foundations
retain the [correctness ledger's](correctness.md) trust boundary.

## Execution and rejection evidence

[`inline-check-test`](../../test/klara/compile/inline_check_test.clj) compares
original Core, actual residual T0 and installed code for shadowing, captures,
multiple copies, nested helpers, zero-arity helpers, unused arguments and Long
boundaries. It rejects changed arguments, duplicate binders, broken freshening
and numeric-literal representation changes.

Two additional owned families exercise captured/shadowed scalar RHSs and nested
helpers, including failure in the loop or final consumer. For 36 source/input
combinations, original T0, residual T0, owned execution and installed JVM results
and failures agree. The prior 96-case finite-model bridge remains separate and
retained. These are tested implementation correspondences, not additional model
proofs merely because the tests pass.

`clojure -M:verify` runs these tests and exports both new goal/proof hashes,
kernel acceptance and direct-self-reference checks. Model construction restores
the prior proof environment and adds no proof work to ordinary entry.

Remaining work includes a general source-to-model decoder theorem, full
closure/environment and world-lookup simulation, ownership inference soundness,
consumer extraction, and representation/JVM correspondence. Broader syntax or
allocation transformations must state which of these obligations they rely on.
