# L4 Compilation

## Preparation

`L4.prepare.job` `(compiler/prepare reference opts)` takes closed Code
`reference` and runs, in one job with `(:budget opts)` (default 100000
steps):

1. the recipe `(:recipe opts)` (default `compiler/as-is`) applied to
   `reference`, giving candidate Code;
2. the checker (`L4.check.*`) on `reference` and the candidate;
3. the backend (`L4.lower.*`) on the candidate.

It returns an outcome with `:status` `:ready`, `:rejected` (with `:rule`,
`:message`) or `:exhausted`, and `:report`. A `:ready` outcome carries
`:candidate` and `:premises`.

`L4.prepare.reference` The reference must be Code for a `fn`; for
`(compiler/reference q)`, `q` must name a function definition.

`L4.prepare.recipe-failed` A recipe that throws or returns a non-Code value
gives `:rejected` with this rule.

## Checking

The checker decides `reference ≡ candidate` by comparing terms up to the
following rewrites, applied lazily (only when the two sides differ) and
under a step budget.

`L4.check.delta` A pinned link to a definition whose value is a closure
without basis may be replaced by the closure's term with its globals pinned
to the same world. A late link may be replaced likewise, using the
preparation world, and records the premise `(name, generation)`. A lifted
closure constant may be replaced by its `reify`.

`L4.check.beta` `((fn [x...] b) v...)` with values `v` and a fixed arity
matching the arguments may be replaced by `b` with `x := v`.

`L4.check.let-value` `(let [x v] b)` with value `v` may be replaced by
`b[x := v]`.

`L4.check.let-app` `((fn [x] b) e)` and `(let [x e] b)` are equivalent.

`L4.check.if-constant` `(if c a b)` with constant `c` may be replaced by `a`
if `c` is truthy and `b` otherwise.

`L4.check.prim` A call of a host function in the pure table to constant
arguments may be replaced by its result, if the call returns normally.

`L4.check.alpha` Terms that differ only in the names of bound locals are
equal.

A *value* for these rules is a `:const`, a `:local`, or a `:fn`.

`L4.check.not-equivalent` The candidate is rejected if the comparison fails
without running out of budget. The outcome names the first pair of differing
subterms.

`L4.check.exhausted` Running out of budget during checking gives
`:exhausted`.

`L4.check.premises` The candidate's premises are the premises recorded by
`L4.check.delta` on either side.

## Lowering

`L4.lower.subset` The backend accepts terms without `:perform`, `:handle`,
`:code`, `:esc`, `:def`, `:try` and `:interop`. Others give `:rejected` with
this rule.

`L4.lower.links` A pinned or guarded link is lowered to its value as a
constant. A late link is lowered to a lookup in the effective world at the
time of the call.

`L4.lower.calls` Calls to closures go through the runtime: a closure with an
installed candidate valid in `E` runs compiled; any other closure runs in a
nested machine.

`L4.lower.steps` Compiled code charges one step per function entry and loop
iteration when it runs under a finite budget.

## Execution

`L4.exec.valid` A candidate is valid in world `E` if every premise
`(q, g)` has `(:generation (get E q)) = g`. Validity is cached per world id.

`L4.exec.executable` `(compiler/executable outcome)` returns a callable. It
runs the compiled body if the candidate is valid in `E`, and otherwise
evaluates `reference` in `E`.

`L4.exec.install` `(compiler/install! outcome)` for a reference that is
`(compiler/reference q)` makes calls to `q`, in worlds where the candidate
is valid, use the compiled body. It does not change any world.

`L4.exec.deopt` If a nested callee of compiled code performs an operation it
does not handle, or the budget runs out inside compiled code, the compiled
call is abandoned and the call is evaluated again by the machine from its
start.

`L4.exec.explain` `(compiler/explain f)` returns data on an executable:
reference, premises, validity in `E`, and `:last-path` (`:compiled` or
`:reference`).

## Pinning

`L4.pin.links` `(compiler/pin c w)` returns `c` with every late link replaced by a
link pinned to `w`. A candidate prepared from pinned Code has no premises.

## Retention

`L4.retain.classes` Each candidate's classes are loaded by a class loader
reachable only from that candidate.

`L4.retain.dispatch` The dispatch table holds at most `:candidates-per-name`
candidates per name (default 4), evicting the oldest installed.
