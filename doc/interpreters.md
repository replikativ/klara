# Reading the specification and the CEK interpreter

Klara has two main executable accounts of evaluation. They use different
representations and are compared by tests; the full interpreter-equivalence
theorem has not been proved.

| | Formal small-step specification | T0 implementation |
|---|---|---|
| Source | `spec/src/klara/spec/core.clj` | `src/klara/eval.clj` |
| State | World, fresh-name counter, term | Control, environment, continuation; staging adds build states |
| Local binding | Substitute terms using de Bruijn indices | Keep values in an environment; closures capture locals |
| Pending work | Evaluation contexts reified in terms/outcomes | Explicit continuation frames |
| Transition | ansatz definition `step` | Handwritten `step-state`; ordinary execution uses `drive` |
| Scope | Restricted calculus with staging and lexical handlers | Larger hosted language, including worlds, authority, ownership, host calls and compiler hooks |
| Evidence | Kernel-checked definitions and named metatheorems | Implementation/differential tests; no whole-T0 correctness theorem |

## How the two accounts relate

For a function application, the specification evaluates the function and
argument and substitutes the argument value into the function body. The CEK
machine instead enters the body with an environment containing the captured
locals and the arguments. A local reference looks up its de Bruijn index in
that environment. Explicit frames remember the context to resume afterward.

These are two ways to implement the intended call-by-value meaning of the
shared fragment. A CEK transition can be administrative: remembering an
argument, entering a body or returning through a frame. There is no intended
one-to-one equality between specification step counts and CEK transition counts.
A general correctness proof needs a relation interpreting environments,
closures and frames as specification configurations, with allowance for such
administrative steps and with observations/effects matched.

The formal `step` is a total function for **one** source step. This does not
prove termination of all programs. The metatheory proves properties including
determinism, preservation of well-scopedness, progress modulo the declared
stuck states, and the stated s-m-n result. It does not establish a theorem for
all hosted Clojure operations, authority protocols or JVM emission.

## What we test against what

From the repository root:

```sh
clojure -X:spec-diff
```

`test-spec/klara/spec_diff_test.clj` runs the shared corpus through both paths:

1. The spec front end parses source into its de Bruijn `Tm`.
2. The specification path runs the ansatz-generated Clojure implementation of
   `step` to an observation.
3. A form-by-form translator turns the same `Tm` into T0 Core, adapting unary
   functions and the handler representation.
4. T0 runs that Core with `ev/run`, without enabling the specialization cache.
5. The test normalizes observations and compares values, errors/stuck
   categories, function/capability markers and code syntax.

The current corpus has **69 programs: 65 agreements and four expected
differences**. The differences concern a bad effect target, two cross-stage
persistence cases, and equality on code values. They are listed explicitly in
`known-differences`; an unexpected disagreement fails. This compares end
observations, not paired machine transitions. Closures and capabilities are
normalized to markers, so it is not a proof of arbitrary contextual equivalence.

The test uses the spec parser, bypassing Klara's production expander. The guide
transcripts and other frontend tests cover that additional path separately.
The parser, translator, observation functions and ansatz JVM code generator
remain implementation bridges; the kernel checks do not prove those bridges.
The optional dependency cohort and commands are in [the artifact guide](artifact.md).

To load the whole formal development and run its reference programs, run
`clojure -M:test` inside `spec/`. That includes the metatheory in `props.clj`;
the differential suite alone loads the executable semantics, not every proof.

## A reading order for T0

Read `src/klara/eval.clj` in this order:

1. **Namespace description:** the machine, effects, world bases, authority and
   deoptimization contracts.
2. **`run`, `drive`, `step-state` near the end:** entry, repeated transition
   dispatch and the one-transition interface. `step-state` is handwritten
   Clojure, not the kernel-checked `step` in the spec.
3. **`step-eval` and `step-ret`:** the central rules. The first dispatches on
   term operations; the second consumes the top continuation frame.
4. **`eval-list` and `finish`:** evaluate operands left to right, collect their
   values and apply the operation.
5. **`Closure`, `lookup`, `enter-closure`, `call-value*`:** values, captured
   environments, argument binding and function/continuation calls.
6. **`do-perform`, `dispatch-clause`:** locate handlers, capture frames and
   resume under the handler protocol.
7. **`start-code`, `step-build`, `step-ret-stage`, `run-code`:** construct
   staged syntax, splice and run it. Read these after the ordinary evaluator.
8. **Authority and deoptimization sections:** their frames extend the same
   machine, with additional admission, cleanup and recovery rules.

The ordinary environment is:

```clojure
{:locals [captured-or-bound-values]
 :basis pinned-definition-root
 :mint basis-for-new-closures}
```

`:basis` selects definitions for execution. `:mint` controls the basis attached
to newly created closures; definition-time evaluation uses `nil` to create
open closures. `:locals` holds lexical values, with de Bruijn index zero
selecting the most recently bound value. Each frame saves the environment it
needs when evaluation returns.

## Step through a tiny pure term in a host REPL

```clojure
(require '[klara.core :as c] '[klara.eval :as ev] '[klara.world :as w])

;; (let [x 41] (+ x 1)) in Core.
(def term (c/let1 (c/quote* 41)
                 (c/prim '+ (c/local 0) (c/quote* 1))))
(def initial [:eval term
              {:locals [] :basis w/empty-root :mint w/empty-root}
              '()])
(def s1 (ev/step-state initial))
;; Evaluating 41, with a :let frame remembering the body and environment.
(mapv :tag (nth s1 3))
;; => [:let]
(def s2 (ev/step-state s1))
(take 2 s2)
;; => (:ret 41)
(def s3 (ev/step-state s2))
(:locals (nth s3 2))
;; => [41]
(ev/drive initial)
;; => 42
```

The other modes are `:build` for staged construction and the five-element
state `[:finish node values env kont]`. A terminal `:ret` has an empty
continuation. Stepping an arbitrary state is not a sandbox or a preemptive
time budget: a transition can call host code, and abandoning live frames can
require authority cleanup. The tiny example above has no such effects.

## Ordinary execution and explicit transitions

The default `drive` uses a fused Clojure dispatch loop. Quotes, local lookups
and closure creation in operand position do not each allocate a machine state
and a list frame. Driver registers live in loop locals. Suspended work still
uses immutable frames in the existing format; capture, resumption and deopt do
not retain a reused mutable driver object.

Selected arithmetic primitives with zero to two exact `Long`/`Double` operands
also use fixed-arity invocation. Their actual function identities must match
the anchored primitives. These operations cannot call back into guest code,
so they do not need a fresh `*outer-k*` binding. Other values, host overrides
and primitives use the original host path. Checked arithmetic and exception
dispatch remain in place; this is not inferred primitive-loop compilation.

`step-state` and `drive-reference` retain explicit transitions. In a host REPL,
bind `ev/*reference-driver*` to `true` to select the original driver, including
for nested host callbacks. Bounded planning still uses `step-state`; its step
accounting is not replaced by fused-driver iteration counts.

`test/klara/driver_test.clj` compares values, errors, output and effect traces,
including multi-shot capture, host callbacks, staging and authority forks. It
also checks generated arithmetic expressions against Clojure and exercises
fallback for custom numbers and overridden primitive functions. Full T0 and
specialization tests exercise the default driver. These are empirical
correspondence checks, not a proof that the fused driver implements the full
CEK transition system. Measurements live in the
[interpreter experiment](../experiments/interpreter/README.md).

## Loops in the interpreter and compiler

Surface `loop`/`recur` expands into a local recursive function and applications.
T0 therefore evaluates a loop with ordinary CEK rules: evaluate the function
and arguments left to right, enter its body with captured locals plus the new
arguments, and continue with the pending continuation. In a self-tail call,
the caller has no further work, so another caller continuation is unnecessary.
This does not by itself remove argument, environment or call-dispatch costs.

The admitted compiled path can represent that same transfer as loop locals and
a jump. For `(recur (inc i) b (+ a b))`, all three next values are computed
from the old `i`, `a`, `b` before any loop local is overwritten. The shared
[`compile/loop.clj`](../src/klara/compile/loop.clj) structural view now feeds the
scalar analyzer and numeric layout inference; scalar emission consumes its
ordered transfer plan. Types, ownership and effect restrictions are separate
admission conditions. This is compiler consolidation; T0's transition rules
and interpreter implementations are unchanged.

## The additional restricted CEK proofs

`verification/consolidation/scalar_cek.clj` and `scalar_finite.clj` formalize a
smaller scalar CEK machine and scoped finite environments in ansatz. They prove
preservation, a transition budget, termination and results for their admitted
syntax. Their tests compare handwritten observers with actual T0 execution.
These strengthen the restricted correspondence work; they do not make the
full handwritten `klara.eval` interpreter a kernel-verified implementation.
