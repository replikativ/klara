# 8. Compilation: a guarded cache

T0 defines what a Klara program means. The first compiling tier turns a
supported function into Clojure code, compiles it with Clojure's public
`eval` API, and installs the resulting function in the specialization
cache. HotSpot optimizes that generated code. Compilation is explicit;
there is no automatic hotness policy.

```
core → source checkpoints / frame states → guarded world inlining → K1 effect classification
     → known HOF recognition → partial evaluation → escape analysis / scalar replacement
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

```clojure klara-repl
k=> (defn pair-sum [x] (let [v [x (+ x 1)]] (+ (first v) (second v))))
#'pair-sum
k=> (pair-sum 4)
9
k=> :repl/compile pair-sum
;; compiled pair-sum: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 4; allocations removed 1
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

```clojure klara-repl
k=> (defn helper [x] (+ x 1))
#'helper
k=> (defn twice-helper [x] (* 2 (helper x)))
#'twice-helper
k=> :repl/compile twice-helper
;; compiled twice-helper: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 5; allocations removed 0
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
its usual error. Entry fallback precedes effects; a failed guard inside a body resumes from a frame state.

Deleting a cache with `klara.stage/clear!` restores generic execution.
The compiler never changes the world's definition values.

## Calls between executables

A world call left after bounded inlining can call another installed
executable directly. Each emitted call site caches resolution by basis-root
and closure-mint identity, then caches the callee's executable using S7's
per-root validity verdict. A hot call checks identities and arity; it does
not look up the dynamic executable cache or construct a T0 machine.
T0's closure entry also reuses these verdicts, and calling an installed
closure from Clojure can bypass machine construction entirely.

The default inlining budget is four definitions. This chain leaves a call
to `abi-base`, which has its own executable:

```clojure klara-repl
k=> (defn abi-base [x] (* x 2))
#'abi-base
k=> (defn abi-one [x] (abi-base x))
#'abi-one
k=> (defn abi-two [x] (abi-one x))
#'abi-two
k=> (defn abi-three [x] (abi-two x))
#'abi-three
k=> (defn abi-four [x] (abi-three x))
#'abi-four
k=> (defn abi-caller [x] (+ 1 (abi-four x)))
#'abi-caller
k=> :repl/compile abi-base
;; compiled abi-base: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 4; allocations removed 0
k=> :repl/compile abi-caller
;; compiled abi-caller: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 9; allocations removed 0
k=> (abi-caller 3)
7
k=> (defn abi-base [x] (* x 100))
#'abi-base
k=> (abi-caller 3)
301
```

From Clojure, `compile-def` accepts `{:inline-fuel 0}` to retain all world
calls. Compilation validates the callee and its transitive fallback region;
unsupported capturing operations or recursive world-call cycles decline
compilation. Install callees separately to enable direct calls. A missing
callee executable falls through ordinary cache entry to T0. A changed root
or cache installation/clear causes selection again; pinned fibers retain
their definitions and valid executables.

ABI v1 inherits the basis, mint, enclosing exception/authority frames,
fiber, authority store and feedback. It introduces no handler or authority
frames. An enclosing resumable exception handler forces T0 entry; ordinary
exceptions unwind to the caller. Deopt is caught at the callee that owns
the frame state: only that callee resumes in T0, then returns to its
compiled caller, without repeating completed effects. General continuation
capture through a compiled JVM frame remains unsupported.

Compiled calls carry an explicit internal context and keep the boxed ABI
adapter for fallback. Scalar entries can avoid dynamic Var bindings;
entries that may invoke host protocols retain their boundary bindings.
These choices do not change results, pinned definitions, handler behavior,
or cache deletion. The [performance evidence](../engineering/performance.md) records the
admission rules and performance limits.

## Known higher-order functions

Local closures and guarded world definitions can be compiled as callbacks
for single-collection `mapv`, three-argument `reduce`, `some` and `every?`.
The callback body runs as emitted code. `mapv` and `reduce` use an indexed
loop with that body inlined when the input has exactly the public JVM
class `clojure.lang.PersistentVector`; other inputs use Clojure's public
operator with an emitted callback. The compiler licenses those calls only
for known public traversal results (`range`, constructed lists/vectors,
`vec`, `map`, `filter`, `mapv`). A raw collection parameter to `mapv` or
`reduce` requires an exact vector entry guard; other argument classes run
in T0. Custom reducing protocols can retain callbacks, so they cannot
receive an emitted callback.

```clojure klara-repl
k=> (defn shifted [xs n] (let [step (fn [x] (+ x n))] (mapv step xs)))
#'shifted
k=> :repl/compile shifted
;; compiled shifted: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 7; allocations removed 1
k=> (shifted [1 2 3] 10)
[11 12 13]
k=> (shifted '(1 2 3) 1/2)
[3/2 5/2 7/2]
k=> (defn sum-even [xs] (reduce (fn [a x] (+ a x)) 0 (filter (fn [x] (even? x)) (map (fn [x] (+ x 1)) xs))))
#'sum-even
k=> :repl/compile sum-even
;; compiled sum-even: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 8; allocations removed 0
k=> (sum-even [0 1 2 3 4 5])
12
```

`map` and `filter` compile only as direct collection arguments of these
eager consumers, two-argument `into`, or `vec`, including nested pipelines.
Their public Clojure lazy operators are retained: an eagerly consumed map
can still run callbacks a chunk ahead of its consumer. No transformation
fuses across these lazy stages. Effects and exceptions retain that order;
`some` and `every?` retain their usual short circuit behavior.

Returning a callback-bearing lazy sequence, or binding it to a local before
consuming it, currently declines compilation. Transducers, multiple input
collections, reduce without an initial value, unknown callbacks, variadic
callbacks and unsupported callback control also decline. Ordinary authority
operations remain supported; an enclosing lexical handler cannot be called
through a host callback, matching T0's host boundary.

Optimized host calls add entry guards for dynamic `:host/call`/`:host/var`
handlers and the identity of the relevant public Clojure function roots.
These guards propagate through direct world calls; a failed guard enters
T0 before effects. The rewrite counts are recorded in the `:lower` pass
log. The [performance evidence](../engineering/performance.md) states each obligation and
the limits of the differential evidence.

## Speculation and deopt

S9 emits a numeric fast path for binary `+` after a top-level let spine.
It checks that a trivial first operand is a JVM Long before unboxing it;
when both operands are trivial it checks both. A failed check resumes T0
at that addition, using a compiler-generated frame state. Earlier effects
are not replayed. Elided local vectors and closures are rebuilt from live
fields and source positions; authority tokens remain live references.

```clojure klara-repl
k=> (defn paid-add [e x] (let [paid (spend! e 1/4) y (* x 2)] (+ y 1)))
#'paid-add
k=> :repl/compile paid-add
;; compiled paid-add: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 4; allocations removed 0
k=> (let [e (evidence 1)] [(paid-add e 1.5) (remaining e)])
[4.0 3/4]
k=> (let [e (evidence 1)] [(paid-add e 2) (remaining e)])
[5 3/4]
```

The first call fails the Long check after spending once. After three
deopts at the same `(CodeId, source path)`, cache feedback disables that
fast path and the emitted code uses ordinary generic addition. This does
not require recompilation. Feedback is an optimization policy, not type
evidence. Single self-tail loops in the top-level let spine also have a
checkpoint at the loop body entrance. A failed Long check reconstructs
the recursive closure and current boxed loop values there. Earlier
iterations are not replayed. Checkpoints inside arbitrary branches and
handlers, and checkpoints with virtual maps or sets, are not generated yet.

## Representations and unboxing

Compiled entries have a fixed arity, checked before running the body.
For closed numeric self-tail loops, the emitter checks the initial JVM
classes and uses primitive long or double loop locals when every backedge
is known to preserve that class. Checked `+`, `-`, `*`, `inc` and `dec`
keep Clojure's overflow behavior. Division, promotion and unknown calls
do not establish that invariant and retain the boxed path. A guard is
type evidence; feedback alone never permits a coercion.

```clojure klara-repl
k=> (defn sum-to [n] (loop [i n s 0] (if (> i 0) (recur (dec i) (+ s i)) s)))
#'sum-to
k=> :repl/compile sum-to
;; compiled sum-to: speculate -> inline -> lower -> pe -> escape -> pe -> emit
;; guards 4; allocations removed 0
k=> (sum-to 4)
10
k=> (sum-to 2.5)
4.5
```

Values are boxed when returned or placed in a deopt frame state; equality,
hashing and ratio results keep their ordinary semantics. Clearing the
cache restores T0 execution.

## What compiles

Fixed-arity functions containing primitives, lets, branches, single-function
self-tail loops, inlinable world functions, guarded direct world calls,
locally called closures, the known HOF combinations above and local
vector/keyword-map projections are supported. Algebraic rewriting
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
host/world/staging calls outside the whitelist, unknown higher-order calls, escaping closures,
mutual recursion, non-tail recursion, variadic functions and frame-creating
authority operations (`fork`, `direct`, `use`) are not emitted. A failed
`:repl/compile` reports the unsupported construct and installs nothing;
ordinary evaluation still works.

There is no general unboxed layout, bytecode emitter, partial escape
analysis, standalone common-subexpression elimination, or automatic
recompilation yet. Unknown calls conservatively escape their arguments;
scalar replacement requires **every** use of an allocation to be safe.
See the [performance evidence](../engineering/performance.md) for the call contract,
validation, Java/Clojure measurements and remaining backend decisions.
