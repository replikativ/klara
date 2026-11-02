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
`klara.jit.staged/residual` (guest code in `lib/`, the staged interpreter of
[08-staged-jit.md](08-staged-jit.md)) unfolds and folds.

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
(for example a numeric type) and a checker that can use them. Such
candidates carry a certificate instead: an [ansatz](https://github.com/replikativ/ansatz)
proof against the formal semantics, whose assumption becomes a runtime guard
(L4.check.certificate, spec/formal/README.md).

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
handlers or staging operations, except in the reference branch of a
speculation, which is left to the interpreter (L4.lower.subset). Compiled
code calls other functions through the runtime: compiled callees directly,
interpreted callees through a nested interpreter. When compiled code cannot
go on (a failed speculation, a nested callee that performs an effect it does
not handle, the budget running out) it *leaves*: it hands the interpreter a
frame state, the node to continue at with the values of the live locals and
the enclosing `let` frames, and the interpreter continues from there.
Nothing is re-executed (L4.exec.leave, L4.exec.frame-state). Host exceptions
propagate unchanged, since the region contains no handlers.

**Budgets in compiled code.** Compiled code charges one step per function
entry and loop iteration (L4.lower.steps). Running out inside compiled code
leaves in the same way, so the job's continuation resumes where it stopped.

## Scheduling is a policy

When to prepare is a separate decision from how:

| Schedule | Written as |
|---|---|
| ahead of time, for a release | `(compiler/prepare (compiler/pin (compiler/reference 'app/main) release-world))`, or from saved profiles (L4.profile.saved) |
| before first use, at load | `(compiler/optimize! 'demo.score/score)` at the end of the namespace |
| when the time spent pays for it | the investor between forms: `(klara.host.api/automatic-investor! session pol)` runs `investor/tick!` (L4.jit.tiers, L4.jit.trigger) |
| never | the default |

A **policy** is guest code and data. Today it is the investor
(`klara.investor`, Klara code) with its thresholds (`investor/policy`: the
interpreted time that pays for compiling as is, and for exploring
alternatives); it can be edited and tested like any other code. It cannot
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
  unboxing, fusion. The prototype has most of these. Each returns as a
  recipe plus a checker rule with a stated proof obligation, or a
  certificate, not as a hidden pass. Ownership-based allocation removal has
  returned this way (04-ownership.md, L4.check.in-place).
- Background compilation. `prepare` is synchronous and bounded.
- Learned policies. The interface is ready for them; the first policies are
  thresholds.
