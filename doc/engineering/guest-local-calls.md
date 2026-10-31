# Guest analysis and checked local-call preparation

This slice moves a real use analysis into ordinary Klara definitions while
keeping its accepted rewrite small. It extends the existing preparation job,
backend and `Prepared -> prevalidate -> install!` lifecycle. It does not add a
second optimizer runtime or accept arbitrary rewritten code as equivalent.

The [funded strategy interface](preparation-strategies.md) now orders this
recipe explicitly, captures a reference subject separately from the policy
root, and retains opaque checked edges behind diagnostic receipts. The guest
preparation request normalizes unsupported regions to `:declined`, malformed
actions to `:rejected`, and spent budgets to `:exhausted`; successful legacy
`:stage/prepare` still returns Prepared directly.

## One optimization through the whole system

Consider:

```clojure
(fn [n]
  (let [score (fn [x] (+ (* x x) 1))]
    (loop [i 0 total 0]
      (if (< i n)
        (recur (inc i) (+ total (score i)))
        total))))
```

The optional pass has five steps:

1. The frontend supplies bounded, uniquely named Core. A hosted adapter creates
   a read-only node table with child indices, binding identities and arities.
   It marks a loop function transparent only when the shared loop validator
   establishes direct entry and nonescaping self-tail use. Literal objects and
   construction capabilities are not exposed to the analyzer.
2. A world-defined Klara analyzer walks each candidate binding's uses. A direct
   call with the expected arity is admissible. An ordinary value use or capture
   under an arbitrary nested function is an escape. Internal validated loop
   functions can be traversed without treating them as escaping closures.
3. The guest returns a proposal containing the exact input identity and selected
   binding indices. The hosted checker independently runs escape analysis and
   checks that every use is an exact-arity direct call. The proposal cannot
   choose its own checker or supply replacement IR.
4. A fixed recipe copies the function body with fresh binders and inserts
   ordered argument lets. Even an unused argument evaluates once, and repeated
   parameter references do not repeat argument effects. The original local
   function allocation can then disappear. Residual size is checked again.
5. The existing baseline emitter lowers the result. The executable retains the
   original Core entry identity, runtime dependencies and guards. A receipt
   records the checked rule, source/residual identities, selected sites,
   analyzer dependencies and metered transitions.

The guest analyzer therefore affects which optimization is attempted. The
checker and fixed recipe determine which changes are accepted. A deliberately
incorrect guest analysis is rejected before emission; it does not license a
different rewrite.

The node table is a temporary projection of the existing named IR. Public Code
views carry opaque construction cursors; the pure service instead receives
inert descriptions that fit its metering/data contract. The adapter and public
views share operation/child/binding concepts, but are not yet one general
inspection interface. Consolidating those adapters is preferable to adding
separate executable representations for each optimization.

The implementation is [local_calls.clj](../../src/klara/compile/local_calls.clj).
The independent checker reuses existing hosted escape/loop analysis. Its
semantic correctness and the recipe's implementation remain tested bridges;
no new universal ansatz theorem is claimed.

## The staged guest program

The [guest module](../../examples/compat/klara/local_optimizer.cljc) contains
the analyzer, a planner generator and a preparation wrapper. `planner-code`
uses `code`/`esc` to embed a minimum call-site count into a pure residual
planner. This threshold is a policy choice about syntax, not a learned estimate
of runtime profitability. Residual compiler-service calls contain no staging
or ambient effects.

With `examples/compat` as a guest source root:

```clojure
(require '[klara.local-optimizer])
(def source
  (code
    (fn [n]
      (let [score (fn [x] (+ (* x x) 1))]
        (loop [i 0 total 0]
          (if (< i n)
            (recur (inc i) (+ total (score i)))
            total))))))
(def kernel (run source))
(klara.local-optimizer/prepare-code source)
;; => {:status :installed, ...}
(kernel 5)
;; => 35
```

The wrapper prepares inside an authority fork, adopts the candidate and requests
installation after leaving the fork. The same function can be called before
first use or later during operation. Loading the module has already executed
its generator; this example does not accelerate that initializer or persist
native artifacts.

## Before-use job and world evolution

Host callers can give the existing preparation job a planner symbol:

```clojure
(require '[klara.compile.prepare :as prepare]
         '[klara.load :as load]
         '[klara.stage :as stage]
         '[klara.world :as world])
(def w (world/make-world))
(load/load-file! w "examples/compat/klara/local_optimizer.cljc" {})
(def cache (stage/make-cache))
(def job
  (prepare/job {:local-call-planner 'klara.local-optimizer/planner}))
(load/load-string! w "(defn increment [x] (let [f (fn [y] (+ y 1))] (f x)))"
  {:prepare :baseline :cache cache :preparation-job job})
```

The planner is resolved in the exact preparation root. Direct `compile-def`
options and `staged/prepare` with `:backend :baseline` accept the same
`:local-call-planner` option. Without it, the mandatory-only baseline continues
to skip this analysis and rewrite. Nothing implicitly installs compiler source.
An explicit host bootstrap is available for the reference analyzer definitions.

Compiler edits are ordinary world edits: a fork can generate another planner
and prepare a candidate without modifying the parent. The checked recipe fixes
the rewrite's meaning, so compiler reads are provenance rather than operational
runtime dependencies. Tests install a candidate made with a child-only planner
in a parent where that planner is absent. This does not waive guards on any
world definitions that the *optimized program itself* reads or calls.
World adoption and executable cache publication remain separate operations.

Binding names in the node table come from uniquely named IR. A service cannot
capture source bindings by inventing a printed symbol; selections are checked
against the original node table. This lexical contract does not complete
[module and phase hygiene](bindings-and-modules.md).

## Budgets, declines and costs

The analyzer runs through the existing pure compiler-service interpreter, with
native hooks disabled. Its definition dependency closure is checked before
execution. The initial limits are 128 view nodes, eight candidate functions and
16,384 service transitions, within the enclosing file/session allowance. The
service data and source caps also apply. Functions with no local-function
bindings skip view construction and service invocation; they keep the broader
baseline source allowance. Each guest invocation is one pass. The
[composition driver](recipe-composition.md) now performs two rounds by default,
with an explicit `:rewrite-rounds` allowance of one through four. Every round
re-analyzes its residual and shares the job budget.

Every rewrite traversal and body-copy reservation spends job work. The residual
must meet the caller's definition node/depth/literal limits before backend
emission. Failed analysis and oversized results retain their charges. These
counters are not wall-clock preemption or exact JVM/GC accounting. Exact boxed
Integer metadata is accepted as inert compiler-service data, preserving its
class rather than coercing quoted runtime values.

Tests cover multiple helpers, branches, nested loops, captured numeric values,
representation-sensitive observations, ordered/unused arguments, exceptions,
forged proposals, escaping closures, effectful and divergent services, residual
growth, file loading, staged generation and actual fork/install execution.
The [regressions](../../test/klara/compile/local_calls_test.clj) also ensure an
optional planner does not narrow baseline coverage when no analysis is needed.
Clean aggregate checks pass: 260 tests / 7,316 assertions and verification
141 tests / 3,490 assertions. The new focused namespace contains 11 tests /
141 assertions.

The [warm diagnostic](../../experiments/baseline/STAGED-LOCAL.md) separates
execution, planning/compilation, installation and module-loading costs. Native
execution is already useful; repeatedly interpreting compiler services is a
remaining preparation cost.

## Next consolidation

The [two-round composition probe](../../experiments/baseline/STAGED-COMPOSITION.md)
now exercises wrapper inlining, re-analysis, helper inlining and conditional
layout inference. It rejects stale or forged layout facts and compiles the
final residual under its own entry identity. The production job now has a
bounded checked driver; the probe continues to test the fact contract and
fresh layout analysis on successive residuals.

The next interface should carry checked facts from one recipe to the next:
binding uses, layouts, effects, source assumptions and output size/cost. Facts
must name their source and their validity conditions; a rewrite must preserve
them or request re-analysis of its residual. Do not treat a prior analysis as
valid merely because a later pass preserves printed names.

For example, inlining a helper can expose arithmetic that layout analysis can
then prove primitive. Conversely, a captured unknown accumulator value prevents
that proof even when inlining is valid. The current pass rechecks the residual
and leaves layout inference to the existing backend/compiler path; it is not
yet a shared general fact representation or a general staged compiler theorem.

The focused proof task is ordered fixed-arity call expansion with fresh
parameters, followed by nonescape-based elimination of the original closure.
It must account for values, failures, argument order and lexical/world context;
termination alone is insufficient. A later recipe-composition result can
connect successive checked source/residual relations. Accelerating an edited
analyzer itself also needs a bounded native-service contract; disabling its
metering because its output is checked would lose the resource guarantee.
