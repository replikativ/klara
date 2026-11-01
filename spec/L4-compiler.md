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

`L4.check.certificate` When the rules above do not relate the candidate to
the reference, `(:certificate opts)` may supply a proof. A certifier
registered for its `:kind` states the theorem about the *actual* reference
and candidate terms (quoted into the formal semantics) and checks the proof
with a kernel. The theorem may assume guards on the arguments (for example
`:long`); the executable checks them at entry and falls back otherwise. A
proof that does not check rejects the candidate with this rule.

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
nested machine whose unhandled effects leave (L4.exec.leave).

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

`L4.exec.leave` Compiled code leaves to the interpreter, without re-running
anything, when a speculation fails (the else branch of
`(if guard specialized reference)` marked as a speculation), when a callee
it runs in a nested machine performs an operation that callee does not
handle, and when the budget runs out (inside compiled code or in such a
callee). The machine continues from the rebuilt state; the executable
reports `:last-path :left`.

`L4.exec.frame-state` Every point where compiled code can leave records a
frame state: the interpreter node to continue at, the environment built from
the compiled locals, and the `let` frames around the point; compiled call
sites add their frames as a leave passes through. The rebuilt state is one
the interpreter reaches by evaluating the candidate from the same input.
Compiled code is normalized to A-normal form first, so all enclosing
contexts are `let` frames.

`L4.check.speculate` A speculation `(if g a b)` is equivalent to `r` if `g`
is a guard (a pure host predicate on locals and constants, which cannot fail),
`a` is equivalent to `r` and `b` is equivalent to `r`.

`L4.exec.explain` `(compiler/explain f)` returns data on an executable:
reference, premises, validity in `E`, and `:last-path` (`:compiled` or
`:reference`).

## Profiles

`L4.profile.record` While profiling is on (the default), the interpreter
records, without changing any result: for each function, its entries
(including loop iterations) with the class and, for simple values, the
value of each argument, marked polymorphic or unstable once they vary; for
each call of a Klara function, the count and the callee; for each `if`, how
often each branch was taken. A function's profile counts all entries (`:count`) and those that are not
self calls (`:external`). It also keeps a recent
argument vector as `:sample`: strongly when its elements are scalars or
collections of at most 10000 elements (a bounded retention of one sample per
function), otherwise weakly. `(klara.profile/record! false)` turns recording
off, `(klara.profile/record! true)` on again.

`L4.profile.snapshot` `(klara.profile/snapshot f)` returns the profile of
closure `f` as data: `:entries`, `:calls` and `:branches`, with source
positions.

`L4.profile.saved` A run can save the profiles of the program's functions
that ran, as EDN keyed by definition, the hash of its source form and the
path of each annotated term (`clojure -M:klara run --record FILE`). A later
run given them (`--aot FILE`) compiles each such definition with
`klara.jit/compile!` and the saved profile right after its definition is
evaluated, if its source form is unchanged, so its first call can run
compiled code. Saved stable values are small data only.

## Pinning

`L4.pin.links` `(compiler/pin c w)` returns `c` with every late link replaced by a
link pinned to `w`. A candidate prepared from pinned Code has no premises.

## Retention

`L4.retain.classes` Each candidate's classes are loaded by a class loader
reachable only from that candidate.

`L4.retain.dispatch` The dispatch table holds at most `:candidates-per-name`
candidates per name (default 4), evicting the oldest installed.

## Specializers

`L4.jit.context` `(klara.jit/context q)` returns a map: `:name`,
`:reference` (Code of the definition), `:profile` (its profile snapshot),
`:runtime` (host facts) and `:specializer`.

`L4.jit.function` `(klara.jit/function ctx f)` builds a candidate function
with fresh parameters for the definition's arity, calling `f` with them as
Code; `f` must return Code for the body. The parameters count as bound while
`f` runs (L2.code.extrusion).

`L4.jit.inline` `(klara.jit/callee-code q)` returns Code for the function
definition `q` in the current world, or nil. Inlining a call as
`((fn [p ..] body) args ..)` is accepted by unfolding `q`, so `q`'s
generation becomes a premise of the candidate.

`L4.jit.simplify` `(klara.jit/simplify c)` partially evaluates Code `c`:
it unfolds calls with known arguments, folds pure functions on constants
and selects branches on known tests, within the job's budget. Its result
is a candidate like any other; nothing it does is trusted.

`L4.jit.attach` `^{:klara/specialize f}` on a definition names its
specializer, resolved in the definition's namespace when the JIT runs.

`L4.check.delta-data` A global whose definition is immutable data (not a
function, macro or mutable object) means its value; its generation is a
premise. `(klara.jit/known? c)` tells whether Code `c` is a constant or
such a global.

`L4.check.speculate-value` In a speculation whose guard is
`(klara.jit/same? x c)` for a local `x` and a constant `c`, the specialized
branch must mean the reference with `x` replaced by `c`. `same?` holds only
when `x` is equal to `c` and of the same class, recursively for collections,
so `x` and `c` cannot be told apart.

`L4.check.speculate-assume` In a speculation `(if g S R)`, `S` must mean the
reference where `g` holds: while comparing, an `if` whose test is `g` takes
its then branch, and one whose test `g` negates (`g` = `(not t)`) its else
branch. A guard is admissible if it is total (locals, constants, total
predicates such as type tests, `=`, `identical?`, `not`, `same?`) or if it
is the reference's own test or its negation, which the reference evaluates
first, so the guard fails only where the reference fails.

`L4.lower.direct` Compiled code calls a late definition directly, without
argument checks, when in the current world (and without a mint) the
definition resolves to compiled code that holds there and has no argument
guards; otherwise as any call. The decision is cached per call site and
world, like the resolution itself.

`L4.lower.hint` A host type hint on a let binding (`^booleans`, `^String`) is
a guard in compiled code: where the bound value is an instance of the class,
the body runs with the hint (so the host compiles array and method access
without reflection); where it is not, compiled code leaves to the
interpreter at the body. A wrong hint costs speed, never meaning.

`L4.exec.osr` Where compiled code left to the interpreter inside a loop,
the interpreter enters compiled code for that loop again at its next
iteration, if the candidate still holds in the current world and mint
(L4.exec.valid, L4.exec.mint-safe). The compiled loop continues from the
same arguments the interpreter would have bound, so the result is the
same. `(compiler/explain f)` counts these entries as `:reentries`.

`L4.exec.provenance` Installed code belongs to the world: the definition
keeps its value and generation and lists its executables, so a fork or an
older world has exactly the compiled code it had, and installing inside a
job changes only the job's world. `(compiler/explain f)` returns, besides
the compiled form, the candidate Code the kernel checked (`:candidate`),
the reference, premises, evidence and guards, and `:provenance`: the
specializer, a summary of the profile it used, the world it was installed
in and, when the investor chose it, its decision.

`L4.exec.mint-safe` Compiled code may run under a mint (L1.context.mint)
when its only inner functions are applied where they are made, so it
creates no closure that would need the mint as basis.
