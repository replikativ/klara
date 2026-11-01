# Extending the JIT: rules, effects, representations

Status: design. The staged interpreter (08-staged-jit.md) is the default
specializer and the investor tiers by time spent (L4.jit.tiers,
L4.jit.trigger). This document plans how users and libraries extend what
the JIT knows, in a way the investor sees and the kernel checks.

## 1. Rules

Today an extension is a whole specializer `(fn [ctx default] code)`. The
staged interpreter makes a finer unit possible: a **rule**, a Klara
function consulted at one point of the generation.

```clojure
(defn rule [point ctx env] ...)   ; a binding-time value, or nil to decline
```

| point | what the rule sees | what it may return |
|---|---|---|
| `:app` | the callee and arguments as binding-time values, the call's profile | a value or code for the call |
| `:entry` | the parameters, the entry profile (classes, stable values) | guarded specializations of the body |
| `:if` | the test, the branch counts | a speculation, or a decided branch |
| `:loop` | the loop's variables, inits and body | another loop (unrolled, vectorized, unboxed) |
| `:let` | the bound value and its hint | a representation for the local |

Rules are Klara staged code like the generator itself: they read terms
through views and build code with templates, so hygiene and the extrusion
check hold, and everything they produce is checked by the kernel. A rule
that wants a guard uses `klara.jit/guard` with an admissible guard
(L4.check.speculate); whatever it cannot justify definitionally needs a
certificate (L4.check.certificate).

Rules compose inside one generation, not as ordered passes: at each point
the generator tries the rules in order and falls back to its own case. The
point's continuations (`:then`/`:else`, `:body`) generate the rest with
all rules, so a rule that takes over an `if` or a `let` still lets the
others act inside it.

Implemented (L4.jit.rules): a rule is `{:name n :fn f}`; `f` receives a map
with `:point`, `:view`, the binding-time values (`:fn`/`:args`, `:test`,
`:init`, `:inits`, `:params`), the continuations and `:profile`.

**Where rules come from.** A policy key, `(staged/specialize ctx {:rules [..]})`,
and a world definition, `klara.jit/rules`, that libraries extend. Being a
definition, redefining a rule set retires what it produced (premises).

**The investor.** Alternatives become *the default with rule set S*. Each
candidate's provenance records the rules that fired; the investor measures
the alternatives as before and records in `investor/decisions` which rules
paid off. A rule that never pays can be dropped from exploration by
policy.

## 2. First rules

1. **Class speculation** (done for array parameters). A parameter or
   local the profile always saw with one class: `(instance? C x)` guards a
   body where `x` carries the hint (L4.lower.hint), so array access and
   host methods resolve without reflection. Sources that lack hints get
   them from profiles. `instance?` with a constant class is a total guard.
2. **Primitive numbers.** Loop variables seen only as longs (or doubles)
   become primitive, with overflow and class guards; float semantics stay
   exact (operation order is kept; numerics stage 0).
3. **Domain rules.** A user's algebra: a known interpreter on its program
   (the `calc` result in 08), a regular expression matcher specialized to
   its pattern (the old prototype's `examples/staging/06-regex.md`, to be
   ported as a showcase of a user rule), rewrites justified by ansatz
   certificates (a Horner form).
4. **Vectorization** (section 4).

Record shapes, planned as a rule, are now a representation: records are
host classes (L0.surface.defrecord) and a keyword lookup of a field is a
direct read, as in Clojure.

## 3. Effects, thought through for Klara

Purity today is one bit (L4.facts.pure). Rules need finer facts: a loop
may be vectorized when its body only writes arrays it allocated; a call
may be measured in a job when its effects stay in the job. beichte, which
raster uses, infers a four-point lattice for Clojure code
(`:pure < :local < :mutation < :io`). Klara needs its own classification,
because it has two things Clojure does not: worlds and jobs, which isolate
some effects, and handlers, which give `perform` its meaning.

Ordered by what can contain them:

| class | examples | contained by |
|---|---|---|
| **pure** | arithmetic, persistent collections | nothing needed: may be computed now, moved, shared, dropped |
| **fresh** | writes to arrays and transients allocated in this call | the call: invisible outside it |
| **world** | `def`, world updates | a job: its fork is discarded or adopted |
| **handled** | `perform` | the nearest handler: pure if the handler is |
| **shared** | writes to objects that existed before (an array argument, an atom) | nothing: visible to others |
| **outside** | I/O, time, the host's global state | nothing, and not repeatable |

What each use needs:

- measuring (the investor) and speculative compilation: at most *world*
  (run in a job), or *handled* under a handler that is itself pure; never
  *shared* or *outside*. Today's analysis allows only *pure* and *fresh*.
- vectorizing, reordering, common subexpressions: *pure* or *fresh*.
- parallel jobs (`run-all`): at most *world*, with conflicts resolved at
  adoption.

Higher-order code needs effect polymorphism: the effect of `(mapv f xs)`
is the effect of `f`. The analysis should be relative ("as `f`") and
resolved at the call, as effect rows do in Koka. Time is already an
effect (L3.effect.time), so it is *handled*, not *outside*. The analysis
stays in the trusted base (facts.clj), conservative, and its results are
premises like purity's. To do: state the classes in spec L4.facts, then
replace the boolean.

## 4. Vectorization

raster compiles numerical Clojure by fusing combinators (SOAC fusion) and
lowering loops to Vector API SIMD, OpenCL or Vulkan, with rewrites written
in pattern. For Klara the same idea is a `:loop` rule family:

- a loop over array indices whose body is *pure* or *fresh* and whose
  carried variables are reductions with an associative operator becomes a
  call of a vector kernel;
- the kernel is a host function with a Klara reference definition (its
  scalar meaning), so the checker relates the candidate to the reference
  by unfolding the kernel's meaning, and the host implementation is a
  trusted primitive with that specification (like the pure host table), or
  carries an ansatz certificate;
- floating point: a vectorized reduction reorders additions, which changes
  results. It is admitted only where the program says reordering is
  allowed (an explicit reassociation policy, a numerics stage above 0),
  never by default.

The backend needs to emit Vector API calls, which the bytecode backend
(07-performance.md, step 3) makes natural.

## 5. Plan

1. [x] Rule interface in `klara.jit.staged` (`:app`, `:entry`, `:if`,
   `:loop`, `:let`), provenance of fired rules, the investor's rule-set
   alternatives; spec L4.jit.rules.
2. [x] Class speculation as the first rule; `instance?` as a total guard
   (`klara.jit.rules/classes`, L4.jit.class-hints). Arrays only for now: a
   hint on anything else has nothing to act on until interop is compiled
   (07-performance.md, step 2); parameters only, loop variables later. A
   1000-element sum over an unhinted `long[]`: 60 µs compiled as is, 6 µs
   with the rule. Found on the way: a stable array made the default fail
   (stable values are now only liftable ones); compiled code read unhinted
   arrays by host reflection, 2x slower than the interpreter (10 ms; now
   `java.lang.reflect.Array`, L4.lower.arrays); and a hinted let's own class
   test was reflective (Sieve 1.23x → 1.02x Clojure).
3. Effect classes in L4.facts (section 3), replacing the purity bit.
4. [x] The regex showcase as a user rule (`showcases/regex.clj`). The
   default alone already compiles Pike's matcher for a stable pattern once
   a pattern's sequence folds (counted sequences are plain data): no
   pattern dispatch on the hot path, each `*` a call of the generic `star`.
   The rule, the matcher staged by hand with a loop for `*`, needed the
   checker to relate a loop to a recursive definition (L4.check.fix,
   fixpoint induction; proof open) and `and`/`or` of tests to the `if`s
   they mean (L4.check.bool-let, L4.check.commute), and templates to carry
   a `recur` across holes (L2.code.recur). The checker caught a real bug in
   the first version of the rule: it skipped the interpreter's `(inc i)`
   where the rest of the pattern is empty, which differs for a position
   that is not a number; the showcase keeps that variant as the rejected
   one. Per match: interpreted ~30 µs (the investor's measurement), the
   default ~0.8 µs, the rule ~0.6 µs (Clojure running the generic matcher
   0.8–1.8 µs, the hand-staged one ~0.36 µs, java.util.regex ~0.15–0.3 µs,
   all under load). Open: how a library adds to `klara.jit/rules` (a
   definition in another namespace cannot be redefined from there; the
   showcase attaches the rule to `matches?` instead).
5. Primitive loops; then vectorization with the bytecode backend.

Before step 2: whether a rule pays is the investor's measurement, so that
came first. Towers and List varied with how the investor measured, not
with its choices (07-performance.md, "Why they varied"); fixed.
