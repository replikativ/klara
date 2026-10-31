# Specialization: guards, evidence, chains and profiles

Status: design. Builds on [02-compilation.md](02-compilation.md); parts are
implemented (single checked steps, generation premises, argument guards from
certificates, AOT by pinning), the rest is planned.

The goal: Klara programs adjust Klara programs, from fully dynamic (JIT
guided by profiles) to fully static (AOT with every guard proved away), while
the interpreter and the checker stay fixed.

## A candidate is code, guards and evidence

| Part | Meaning | Examples |
|---|---|---|
| Code | the implementation, checked against a reference | an unrolled loop, a transient accumulator |
| Guards | conditions checked at entry; if one fails the next candidate runs, finally the reference | world premise `(power, 40)`; argument guard `x : long`; value guard `coeffs = [1 2 3]` |
| Evidence | why the code means the same as the reference while its guards hold | definitional, proved, tested, trusted |
| Provenance | how it was produced | the recipe chain, the profile it used |

**Evidence kinds**, in decreasing strength:

- *definitional*: the kernel checker (L4.check.*), automatic;
- *proved*: a certificate checked by a kernel (L4.check.certificate);
- *tested*: the candidate agreed with the reference on recorded samples
  (profile inputs); evidence about those inputs only;
- *trusted*: the program asserts it.

Which kinds a job accepts is policy: by default definitional and proved;
tested and trusted only when the session or job enables them explicitly, and
`compiler/explain` always reports the kind. (Open decision: whether trusted
evidence should exist at all.)

## Fixed hooks in the runtime

The interpreter has exactly three:

1. at a call, select an installed candidate whose guards hold;
2. otherwise run the reference;
3. count calls and sample argument shapes into profile data.

Profiles are values (`klara.profile/snapshot`): they can be inspected,
stored in a world, saved with a build and fed to a later AOT preparation.

## Composition is a chain

A rewrite pipeline is a sequence of steps. Each step is a recipe (a Klara
function from Code to Code), checked against the previous step's output, with
its own evidence and guards. Evidence composes by transitivity; the guards of
the final candidate are the union.

```text
reference ──fuse──▶ R1 ──horner──▶ R2 ──longs──▶ R3
          definitional    proved, |x| ≤ 2^20    guarded: xs is a long vector
```

Fusion (control flow, justified by unfolding `map` and `reduce`) and Horner
(arithmetic, justified by a law under a range premise) are different kinds
of rewrite only in their evidence; as steps they are the same thing.

## DSLs and staged generators

A DSL's reference is its interpreter; its compiler is a staged generator.
The candidate relates them: reference `(fn [x] (run-dsl prog x))`, recipe
`(fn [_] (gen-dsl prog))`. For a static `prog`, unfolding the interpreter is
the first Futamura projection, which is what the definitional checker does,
so many generators need no proof.

**genlet** is an effect. `(genlet c)` performs `:stage/genlet`; the nearest
`code` construction in progress handles it by binding `c` to a fresh name at
its top and returning the name. Moving computation earlier is safe only for
pure, total expressions; in a recipe, an unsafe placement fails the check
unless it carries other evidence.

## From dynamic to static

| Mode | Prepared when | Guards from | Left at run time |
|---|---|---|---|
| Interpreted | never | — | the reference |
| JIT | after a policy's threshold, reading profiles | profiles, generation premises | entry guards, fallback |
| AOT | at build, pinned to a release world | earlier profiles; no generation premises | undischarged guards |
| Static | at build | discharged at every call site | nothing |

**Guard discharge** is a property of a call site: if the caller's candidate
establishes the callee's guard at the call (literal types, the result type of
checked arithmetic, a certificate), the call goes to the guard-free entry.
Because the reference ships with the program, speculation in an AOT build is
safe: a failed guard costs speed, not correctness.

## Plan

1. Chains of steps in `compiler/prepare` (`:steps`).
2. Argument and value guards for every step; evidence kinds and a policy.
3. Profile data in the interpreter; a threshold policy written in Klara.
4. genlet as an effect handled by code construction.
5. Guard discharge at call sites; AOT given a profile.
6. Ownership as a step kind ([04-ownership.md](04-ownership.md)).
