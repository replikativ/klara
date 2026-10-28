# 8. Compilation: a guarded cache

T0 defines what a Klara program means. The first compiling tier turns a
supported function into Clojure code, compiles it with Clojure's public
`eval` API, and installs the resulting function in the specialization
cache. HotSpot optimizes that generated code. Compilation is explicit;
there is no automatic hotness policy.

```
core → guarded world inlining → K1 effect classification
     → partial evaluation → escape analysis / scalar replacement
     → partial evaluation → Clojure forms → executable
```

Each intermediate representation is a value. The executable contains the
residual representation, emitted forms, pass log, assumptions and a
`:tested` certificate. These passes are **differentially tested against
T0, not proved**. Compilation does not run a proof checker or test every
possible input to your function.

## Compile a definition

A vector used only through local projections can disappear. Its elements
are still evaluated once, in their original order, including unused
elements that could fail or perform effects.

```klara-repl
k=> (defn pair-sum [x] (let [v [x (+ x 1)]] (+ (first v) (second v))))
#'pair-sum
k=> (pair-sum 4)
9
k=> :repl/compile pair-sum
;; compiled pair-sum: inline -> lower -> pe -> escape -> pe -> emit
;; guards 3; allocations removed 1
k=> (pair-sum 4)
9
k=> :repl/compiled
pair-sum :tested
```

The allocation count is the number of construction sites removed from
Klara's representation. It is not a measurement of JVM allocations.
Installed entries belong to the REPL session and may be shared across its
world forks; their guards are checked against each caller's basis.

## Guards and fallback

Inlining a world definition records `[:world name value-id]`. A changed
or pending dependency fails that guard before the executable runs. T0
then evaluates the original function against the calling basis. Older
forks can still use the executable when their guards hold.

```klara-repl
k=> (defn helper [x] (+ x 1))
#'helper
k=> (defn twice-helper [x] (* 2 (helper x)))
#'twice-helper
k=> :repl/compile twice-helper
;; compiled twice-helper: inline -> lower -> pe -> escape -> pe -> emit
;; guards 4; allocations removed 0
k=> (twice-helper 3)
8
k=> (defn helper [x] (+ x 100))
#'helper
k=> (twice-helper 3)
206
```

The other guards require empty captures, no fixed specialization arguments,
and no active dynamic exception handler. A resumable exception handler
needs T0 frames to continue after a failed primitive; a JVM frame cannot
supply those frames. Wrong arity also declines at entry, so T0 reports
its usual error. No fallback replays a partially executed compiled body.

Deleting a cache with `klara.stage/clear!` restores generic execution.
The compiler never changes the world's definition values.

## What compiles

Fixed-arity functions containing primitives, lets, branches, single-function
self-tail loops, inlinable world functions, locally called closures and
local vector/keyword-map projections are supported. Algebraic rewriting
without numeric type evidence is deliberately narrow: `identity` can go,
but `(+ x 0)` cannot generally be replaced by `x` in an untyped language.

Lexical handlers compile when every clause is visibly abortive (no use of
its continuation) or tail-resumptive (one direct final continuation call).
Their operations become direct calls on the local handler's clause
functions; aborts unwind to that handler instance. Ordinary authority
operations call `klara.authority` with T0's enclosing branch contexts.
A compiled spending function can therefore run inside a T0 fork.

## What stays in T0

General operations, dynamic handlers, handler return clauses, ambient
host/world/staging calls, unknown or higher-order calls, escaping closures,
mutual recursion, non-tail recursion, variadic functions and frame-creating
authority operations (`fork`, `direct`, `use`) are not emitted. A failed
`:repl/compile` reports the unsupported construct and installs nothing;
ordinary evaluation still works.

There is no unboxed representation, bytecode emitter, partial escape
analysis, standalone common-subexpression elimination, or automatic
recompilation yet. Unknown calls conservatively escape their arguments;
scalar replacement requires **every** use of an allocation to be safe.
See [the implementation report](../background/impl/S8.md) for the precise
boundary and measurements.
