# Compilation as checked staging

Klara does not have an optimizer hidden inside the runtime. It has a
pipeline that ordinary programs drive, in which the untrusted part (deciding
what to try and producing code) is separated from the trusted part (deciding
whether the result means the same thing, and running it).

```text
          policy (guest)                     checker (trusted)
               |                                    |
reference --> recipe (guest) --> candidate Code --> equivalent? --> backend --> candidate
   Code          in a job, under a budget            + premises      lower        |
                                                                                  v
                                       call in world E --> premises hold in E? --yes--> compiled body
                                                                 |no
                                                                 +--> reference meaning
```

## The pieces

**Reference.** Closed Code that defines the meaning, for example
`(code (fn [x] (power 3 x)))`. `(compiler/reference 'demo.score/score)` gives
the Code of a definition.

**Recipe.** A function from reference Code to candidate Code. It may do
anything: run a staged generator, call a partial evaluator written in Klara,
or ask an external agent. Recipes are not trusted. The default recipe
`compiler/as-is` returns the reference itself, which is plain compilation.
`klara.compiler.recipes/inline` (guest code in `lib/`) unfolds and folds.

**Job.** `prepare` runs the recipe and the checker inside a job
([00-model.md](00-model.md#effects-handlers-and-jobs-l3)): the recipe cannot
publish anything, its printing is deferred, and it stops when its budget is
spent. The checker's work is charged to the same budget.

**Checker.** Decides whether the candidate is equivalent to the reference
(below) and returns the **premises** that the decision relied on.

**Backend.** Lowers checked Code to a JVM class through the Clojure compiler.
The backend is trusted; it is tested differentially against the interpreter
and its rules are listed in [spec/L4-compiler.md](../spec/L4-compiler.md).

**Candidate.** The executable, its premises, its footprint and a report.

## The checker

The checker compares two terms by *definitional unfolding*, in the style of a
proof assistant's kernel: put both terms in head-normal form, compare heads,
compare subterms, and unfold a definition only when the heads differ. Its
rules:

| Rule | Rewrite | Why it is sound under Clojure semantics |
|---|---|---|
| `L4.check.delta` | a pinned or guarded link to a function definition becomes the function's term | the link denotes exactly that definition |
| `L4.check.beta` | `((fn [x] b) v)` becomes `b[x := v]` when `v` is a value | substituting a value preserves call-by-value evaluation |
| `L4.check.let-value` | `(let [x v] b)` becomes `b[x := v]` when `v` is a value | evaluating a value has no effect |
| `L4.check.let-app` | `((fn [x] b) e)` and `(let [x e] b)` are the same | both evaluate `e` once, first |
| `L4.check.if-constant` | `(if c a b)` with constant `c` selects a branch | Clojure truthiness is decidable on constants |
| `L4.check.prim` | a pure primitive applied to constants is replaced by its result, if computing it succeeds | the primitive is deterministic and has no effect |

A *value* here is a constant, a variable, or a `fn` term. The rules never
drop, duplicate or reorder an expression that could fail, diverge or perform
an effect. So the checker rejects:

- `(* x 1)` for `x`: not definitional, and wrong when `x` is not a number;
- removing an unused `(let [y (f)] ...)`: `(f)` might throw;
- reordering two calls.

These rejections are the point: a recipe that does algebra needs premises
(for example a numeric type) and a checker that can use them. That is
future work, and the natural place to add [ansatz](https://github.com/replikativ/ansatz)
proofs: each new rule must come with a proof against the L0 semantics.

**Premises.** Unfolding a *pinned* link records nothing: the link cannot
change. Unfolding a *late* link means the checker used the definition it
found in the preparation world, so it records `(name, generation)`. The
candidate's premises are the set of these pairs, plus the generation of the
definition being compiled.

**Fuel.** Unfolding is bounded by the job's budget. Running out is
`:exhausted`, not `:rejected`: the candidate may be correct but the checker
could not show it within budget.

## Executing candidates

A candidate is valid in world `E` if every premise `(name, g)` has
generation `g` in `E`. Worlds are immutable, so validity is computed once per
world and cached by world identity. Since an activation's world changes only
at explicit points, a compiled loop runs without further checks.

- `(compiler/executable c)` is a callable that checks validity on entry and
  runs the compiled body or, if invalid, the reference meaning in `E`.
- `(compiler/install! c)` makes calls to the compiled definition use the
  candidate wherever it is valid. Installing never changes meaning; the
  reference definition stays in the world.

**What compiled code may do.** The backend accepts Code without `perform`,
handlers or staging operations. Compiled code calls other functions through
the runtime: compiled callees directly, interpreted callees through a nested
interpreter. If a nested callee performs an effect that is not handled
inside it, the compiled region is abandoned *before the effect happens* and
the call is re-executed by the interpreter from its start (`L4.exec.deopt`).
This is correct because a compiled region performs no effects of its own: no
effect has been observed when it is abandoned. Host exceptions propagate
unchanged, since the region contains no handlers.

**Budgets in compiled code.** Compiled code charges one step per function
entry and loop iteration. Running out inside compiled code abandons the
region in the same way, so the job's continuation resumes at the call.

## Scheduling is a policy

When to prepare is a separate decision from how:

| Schedule | Written as |
|---|---|
| ahead of time, for a release | `(compiler/optimize! (compiler/pin (compiler/reference 'app/main) release-world))` |
| before first use, at load | `(compiler/optimize! 'demo.score/score)` at the end of the namespace |
| after a threshold (planned) | `(compiler/watch! 'demo.score/score {:after 1000 :policy p})` |
| never | the default |

A **policy** is a guest function from an observation map (call count, term
size, previous outcomes) to `nil` or `{:recipe r :budget b}`. Policies are
ordinary Klara code and can be edited and tested like any other. They cannot
make a rejected candidate acceptable.

## AOT by pinning

`(compiler/pin code w)` replaces every late link in `code` by a link pinned to
`w`. Preparing pinned code records no premises, so the candidate has no
guards. A release is the result of pinning the entry points to a release
world and preparing them: the same pipeline as live optimization, with
everything constant. Persisting such candidates across processes is a later
deployment step; the first version compiles in-process.

## What is not in the first version

- Rewrites that need type or numeric premises, loop transformations,
  unboxing, fusion, ownership-based allocation removal. The prototype has
  most of these. Each returns as a recipe plus a checker rule with a stated
  proof obligation, not as a hidden pass.
- Background compilation. `prepare` is synchronous and bounded.
- Learned policies. The interface is ready for them; the first policies are
  thresholds.
