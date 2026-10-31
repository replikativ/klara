# Bounded recipe composition and ordered calls

The [preparation strategy implementation](preparation-strategies.md) extends
this driver with explicit inspect/rewrite/finish control. Exact endpoint edges
are now opaque accepted capabilities; receipt maps remain diagnostic. The
semantic bridges described below remain tested rather than proved.


The preparation path now runs successive checked local-call rounds against one
pinned root and one budget. The driver reuses the existing IR, guest analyzer,
checker and backend. It retains the original function's Core entry identity.
This is the production counterpart of the earlier
[two-round probe](../../experiments/baseline/STAGED-COMPOSITION.md).

## Controller contract

[`compile/compose`](../../src/klara/compile/compose.clj) accepts a hosted adapter
to a checked recipe, a residual bounds validator and a round allowance. It
does not accept an unchecked guest-supplied rewrite function. Its responsibilities
are source/target identity chaining, residual bounds, repeated analysis,
termination of the preparation attempt and accounting. The step checker still
determines semantic admission.

With `:local-call-planner`, the default allowance is two rounds. The optional
`:rewrite-rounds` job/backend option admits one through four. With no planner,
the baseline remains mandatory-only. Each round:

1. Invokes the analyzer on the current residual, without prior analysis facts.
2. Checks the selected bindings and applies the existing ordered inline recipe.
3. Validates residual node/depth/literal bounds before further analysis/emission.
4. Checks that the receipt names this exact input and output and joins the
   preceding receipt. Missing/malformed links and cycles reject.
5. Stops on unchanged source identity or the round limit. A residual can still
   compile after reaching the limit; remaining unsupported constructs decline
   through ordinary backend admission.

Zero calls inlined is not a fixed-point test: deleting an unused closure can
expose another unused closure. The regression covers this case. Compiler reads
accumulate as provenance across rounds, while runtime program dependencies keep
their own guards. Failed work remains charged. Publication occurs only after
all selected rounds, emission and executable validation succeed.

`:rewrite-receipts` contains the chain; `:rewrite-summary` records rounds,
stopping reason and calls inlined. `Prepared` inspection exposes these alongside
compiler provenance. Receipt IDs describe exact named-IR artifacts within the
job; their gensyms are not stable cross-process cache keys.

```clojure
(prepare/job {:local-call-planner 'klara.local-optimizer/planner
              :rewrite-rounds 2})
```

The wrapper/captured-helper example now reaches the original installed entry
through two rounds. Fresh analysis avoids transporting a stale layout or
ownership claim. The driver is not yet a general fact cache or a scheduler for
arbitrary combinations of recipes. See the
[regressions](../../test/klara/compile/compose_driver_test.clj).

## Kernel-checked model result

[`consolidation.ordered-call`](../../verification/consolidation/ordered_call.clj)
defines a stateful model:

```text
evaluate : Argument -> State -> Answer<Value, State, Error>
body     : List<Value> -> State -> Answer<Value, State, Error>
```

`callArguments` evaluates all arguments from left to right, passing the state
from each successful evaluation to the next. A failure carries its resulting
state and prevents later arguments/body evaluation. `callDispatch` enters the
body only after the entire argument list succeeds. `orderedLets` expresses
the nested evaluation/parameter-binding continuation directly.

The kernel accepts `ordered-call-refines` for every finite argument list,
abstract value/state/error types and total model evaluator/body functions:

```text
orderedLets(arguments, evaluate, state, body)
  = callDispatch(callArguments(arguments, evaluate, state), body)
```

The proof uses list induction and two constructor-case lemmas. State can record
the chosen logical effects and failure prefix. Internal binding administration,
physical allocation, timing and optimizer work are not automatically such
observations. The total-function model does not establish divergence or
capturing-control correspondence for arbitrary guest expressions.

`recipe-observations-compose` additionally proves composition under matching
observation functions. If the first recipe preserves source/middle observations
and the second preserves middle/target observations on their respective
domains, their composition preserves source/target observations. This theorem
assumes those correctness premises; it does not discharge applicability,
establish an ownership conversion or let two recipes choose incompatible
middle observations.

All four named theorems are rechecked with no self-reference. Building the model
restores the prior ansatz environment. The normal runtime does not build these
proofs at load time. `clojure -M:verify` exports their goal/proof fingerprints.
The actual recipe regression tests ordered arguments with a host counter,
including failure on the first and second argument.

## Remaining correspondence obligations

The model abstracts parameter binding as an ordered list of values. Connecting
it to the actual rewrite still requires:

* Exact arity and the correspondence between parameter slots and source uses.
* Freshening/alpha-renaming and preservation of free lexical/module references;
  later arguments must not be captured by earlier generated lets.
* The creation/call world context of a nonescaping closure.
* Core/CEK evaluation and the admitted noncapturing control/effect domain.
* Checked numeric and container representations and JVM lowering.

These are tested hosted bridges today, not corollaries of the ordering theorem.
Existing staging well-scopedness results and private-state simulations cover
related smaller models; this work does not silently identify them with T0.

The [ownership family study](../../experiments/baseline/OWNERSHIP-FAMILY.md)
exercises the next handoff: exposing captured helper bodies, re-analyzing for
ownership, then choosing private storage. Its observation restriction remains
material: full host identity can distinguish the result representation.
Ownership inference/native preparation remain a separate path and budget;
they have not been added automatically to this production driver.

Clean standalone checks pass at this milestone: **263 core tests / 7,336
assertions** and **149 verification tests / 3,575 assertions**. The verification
suite includes the new ordering model and the composition/ownership families.
