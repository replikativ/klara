# L3 Effects and jobs

## Effects and handlers

`L3.perform` `(perform op & args)` with a keyword `op` suspends the
computation and passes `args` and the continuation to the nearest enclosing
handler for `op`.

`L3.handle.deep` `(handle handlers body...)` evaluates `handlers`, a map
from operation keywords to functions `(fn [k & args] ...)`, then the body
with a handler frame installed. A handler function runs *outside* the
frame. Its continuation `k`, when called with `v`, resumes the body with `v`
as the value of `perform`, with the frame reinstalled (deep handlers).
`:return`, if present, is applied to the body's value.

`L3.cont.value` A continuation is a function value of one argument.

`L3.cont.multishot` A continuation may be called more than once.

`L3.affine.reuse` A continuation that captured an affine resource (a budget)
may be called at most once; a second call raises this rule.

`L3.effect.default` An operation with no enclosing handler is handled by the
context's default handler: the session's at top level, the job's inside a
job. `:io/print` prints; `:world/define` publishes (L1). Others raise
`L3.effect.unhandled`.

`L3.effect.host-boundary` A Klara closure called by host code (for example
inside `clojure.core/map`) runs in a nested machine with the default
handlers of the current context. Operations that only a handler outside the
host call could handle raise this rule.

## Jobs

`L3.job.run` `(job/run opts thunk)` calls `thunk` in a new activation whose
world is a fork of the current `E` (a new world id with the same
definitions), with the job's default handlers, under the budget
`(:budget opts)`. It returns an outcome map and never throws for failures
inside the job.

`L3.job.outcome` An outcome has `:status` (`:done`, `:failed` or
`:exhausted`), `:world` (the job's final world), `:intents` (deferred
effects in order), `:spent` (`{:steps n}`) and `:value`, `:error` or
`:continuation` according to the status.

`L3.job.define` Inside a job `:world/define` changes the job's world only.

`L3.job.print` Inside a job `:io/print` is appended to `:intents` instead of
printing.

`L3.job.intent-limit` More than `:intent-limit` intents (default 10000) fail
the job.

`L3.job.host-mutation` Inside a job, `swap!`, `reset!`, `vswap!` and
`vreset!` on objects not created inside the job raise this rule.

`L3.job.adopt` `(job/adopt! outcome)` publishes the job's world changes to
the session (as `L1.session.publish`) and then performs its intents in
order. Adopting an outcome twice raises `L3.job.adopted`.

`L3.job.resume` `(job/resume outcome budget)` continues an `:exhausted`
outcome's continuation under a new budget and returns a new outcome.

`L3.job.discard` Dropping an outcome is discarding the job. Nothing needs to
be called, and the parent's spent budget is not reduced.

## Budgets

`L3.budget.steps` A budget limits machine steps: each evaluation transition
costs one step. Compiled code (L4) costs one step per function entry and per
loop iteration.

`L3.budget.exhausted` When a budget reaches zero the job stops with status
`:exhausted` and the continuation at that point.

`L3.budget.nesting` A nested job's budget is reserved from its parent's
remaining budget. Steps spent by the nested job count as spent by the parent.
Unused reserved steps return to the parent when the nested job ends.
