# Specialization: candidates, evidence, the investor

Status: design, partly implemented (single checked steps, generation premises,
argument guards from certificates, AOT by pinning). Speculation inside code,
frame states, facts, profiles and the staged JIT are in
[06-speculation.md](06-speculation.md).

The goal: Klara programs adjust Klara programs, from fully dynamic (JIT
guided by profiles) to fully static (AOT with every guard proved away), while
the interpreter and the checker stay fixed.

## A candidate is code, guards and evidence

| Part | Meaning | Examples |
|---|---|---|
| Code | the implementation, checked against a reference | an unrolled loop, a fused traversal |
| Guards | conditions under which it applies; elsewhere the reference runs | world premise `(power, 40)`; `x` is a long; `coeffs = [1 2 3]` |
| Evidence | why the code means the same as the reference while its guards hold | definitional, proved, tested, trusted |
| Provenance | how it was produced | the steps taken, the profile used, the costs paid |

**Evidence kinds**, in decreasing strength: *definitional* (the kernel
checker), *proved* (a certificate checked by a kernel), *tested* (agreement
with the reference on recorded inputs, evidence about those inputs only),
*trusted* (asserted by the program). Which kinds a job accepts is policy: by
default definitional and proved; tested and trusted only when the session or
job enables them explicitly, and `compiler/explain` always reports the kind.

## Rewrites are planned, not hard-coded

Recipes are the vocabulary: Klara functions from Code to Code, each with the
evidence it can offer. Two rewrites of different character, fusion of
`reduce` over `map` (control flow, justified by unfolding) and Horner's rule
(arithmetic, justified by a law under a range premise), are both recipes;
they differ only in their evidence.

The **investor** is a Klara program that plans which recipes to apply, in
which order, to which functions. A plan is a path through programs:

```text
reference ──fuse──▶ R1 ──horner──▶ R2 ──longs──▶ R3
          definitional    proved, |x| ≤ 2^20    speculative: xs holds longs
```

Each step is checked against the previous one; evidence composes by
transitivity; the final guards are the union.

As built, the composition goes through the world rather than through one
chain: `spec/formal/cases/fused_horner.clj` fuses the caller's fold by a
law (L4.check.law), certifies the callee's Horner form under its range
guard (L4.check.certificate), and the fused loop calls the callee, so each
executable checks its own guards at entry and neither rewrite needs to know
the other. The longs step was dropped (06-speculation.md §4). The investor weighs:

- expected benefit: calls (from profiles) times predicted saving;
- preparation cost: rewriting, checking, proof search, lowering, measured;
- risk: how often the guards are expected to fail;
- retention: memory held by candidates and code.

It may explore alternative plans in parallel forked jobs under budgets, then
settles once: it installs the winner, discards the rest, and pays for all of
them. A fixed list of steps is the degenerate investor, for tests.

## Facts widen the rules

The checker's rules today must hold for any code: they never drop, duplicate
or reorder a computation that might fail, diverge or perform an effect.
Facts about a region (*pure*, *total*, *unique*, from analyses or type
systems, see [06-speculation.md](06-speculation.md)) license further rules,
each with a precondition and proved once for the formal fragment:

| Rule | Precondition |
|---|---|
| dead code elimination | pure and total |
| let floating, code motion | pure and total |
| common subexpression elimination | pure |
| representation change in place | unique |

The longer code is guaranteed free of effects, the more it can be rewritten.
For pure regions, equality saturation (exploring all equivalent programs and
extracting the cheapest by a cost model) becomes available; it needs a
first-order form of the code (closures explicit), and ansatz's `grind`
already provides e-graph machinery.

## Sharing instead of genlet

Generators stay pure: no effect for let-insertion. Code is persistent data,
so a generator that reuses a Code value produces a DAG, not a duplicated
tree; the naive Fibonacci generator builds a linear-size DAG. Let-insertion
is a decision of lowering: each shared node is emitted once, bound at the
closest point that dominates all its uses. Binding it earlier is allowed only
when the node is total (a fact). The checker compares DAGs with memoization
on node identity, so checking stays linear in the DAG.

## From dynamic to static

| Mode | Prepared when | Guards from | Left at run time |
|---|---|---|---|
| Interpreted | never | — | the reference |
| JIT | after the investor decides, from profiles | profiles, generation premises | guards with frame states |
| AOT | at build, pinned to a release world | earlier profiles; no generation premises | undischarged guards |
| Static | at build | discharged at every call site | nothing |

Because the reference ships with the program, speculation in an AOT build is
safe: a failed guard costs speed, not correctness.
