# Formal semantics

A kernel-checked specification of a fragment of Klara Core, written in
[ansatz](https://github.com/replikativ/ansatz) (the Lean 4 kernel in
Java, with a Clojure surface). The total function `step` is the
specification; ansatz compiles it to Clojure, so it is also an executable
reference interpreter.

```sh
clojure -M:formal:test-formal   # check every definition and theorem, run the differential tests (500 programs each)
KLARA_DIFF_SEEDS=5000 clojure -M:formal:test-formal
```

The `:formal` alias uses the [ansatz](https://github.com/replikativ/ansatz)
release pinned in `deps.edn`; `deps.edn` also shows how to use a local
checkout instead.

## Files

| File | Content |
|---|---|
| `src/klara/formal/core.clj` | Syntax (`Tm`), worlds, checked 64-bit primitives, staging with generated names, `ev`, `step` |
| `src/klara/formal/ws.clj` | Well-scopedness: weakening, substitution, pinning, soundness of `run`'s closedness check |
| `src/klara/formal/props.clj` | Determinism, preservation, progress, safety, running quoted code |
| `src/klara/formal/checker.clj` | The checker's head rules are steps; a step preserves the terminal configurations reached |
| `src/klara/formal/certify.clj` | The ansatz certifier for proof-carrying candidates (L4.check.certificate) |
| `cases/certified_identity.clj` | A candidate admitted by proof: `(* x 1)` replaced by `x` for 64-bit integers |
| `cases/proof_search.clj` | Proof search as guest code: a Klara program looks for the certificate in a budgeted job |
| `cases/certified_horner.clj` | Horner's rule admitted by a certificate under the range guard \|x\| ≤ 2^20, computed by a Klara function (bounds by `nlinarith`, values by `ring`) |
| `src/klara/formal/bridge.clj` | The trusted bridge: quoting real Core terms into `Tm`, running the model, observations |
| `src/klara/formal/gen.clj` | A seeded generator of Klara programs inside the fragment |
| `src/klara/formal/acct.clj` | λ-acct, the accounting calculus: syntax, store, `ev` (checked or with the reuse check erased), `step` |
| `src/klara/formal/acct_props.clj` | Conservation |
| `src/klara/formal/acct_typing.clj` | The affine judgment, the invariant, preservation, progress, no-reuse, check erasure |
| `src/klara/formal/acct_bridge.clj` | The trusted bridge for λ-acct: a generator of token programs rendered as Klara source and as λ-acct terms |
| `test/klara/formal/` | Proof check and differential tests |

## The fragment

Integers (checked 64-bit), booleans, `nil`, keywords; `fn` with one fixed
arity (curried in the model), `let`, `if`, `do`, `loop`/`recur`, one
recursive `letfn`; late and pinned global links; `+ - * = < > <= >= inc dec
zero? not`; `perform`/`handle` with literal handler maps; `code`, `esc`,
`lift`, `run`. Outside it: collections, strings, `try`, interop, jobs, the
compiler. Forms outside the fragment are reported, not compared.

## Theorems and the rules they establish

| Theorem | Statement | Rules |
|---|---|---|
| `step-det` | `Step` is the graph of a function | L0.eval.order (determinism of evaluation) |
| `preservation` | a step from a closed configuration yields a closed configuration | L0.term.wf |
| `progress` | a closed configuration is a value, steps, is an unhandled effect, a named error, or a scope extrusion | L3.effect.unhandled, L2.code.extrusion |
| `safety` | no reachable configuration of a closed program is stuck on a free variable | — |
| `ws-subst` | substituting a closed value preserves well-scopedness | L4.check.beta (scoping part) |
| `ws-pinTm` | pinning a value to a world preserves scoping | L1.context.get, L2.link.pinned |
| `wsb-WS` | `run`'s closedness check is sound | L2.run.closed |
| `run-quote` | `(run (code t))` steps to `t` for binder- and escape-free `t` | L2.run.context |

The checker's head rules, each proved for the fragment's form of the rule
(not the implementation's general one):

| Theorem | Statement | Rules |
|---|---|---|
| `beta-step`, `fix-step` | a call of a one-parameter function (curried) on a value steps to the substituted body | L4.check.beta, one argument; the implementation goes through L4.check.let-app, which is not proved |
| `let-value-step` | a let of a value steps to the substituted body | L4.check.let-value |
| `if-true-step`, `if-false-step` | an if on a constant steps to the selected branch | L4.check.if-constant |
| `prim-step` | one of the model's five integer primitives (`+ - * = <`) on constants steps to its result when it succeeds | L4.check.prim, for those five; not the implementation's table of pure host functions |
| `delta-step`, `pin-step` | a late or pinned global steps to its definition | L4.check.delta |
| `step-equiv` | a configuration and its step reach the same terminal configurations | composition |
| `ev-prim-lit`, `ev-prim-l`, `ev-prim-r`, `step-of-ev` | a step inside nested arithmetic is a step of the operand it is in | certificates for straight-line integer code |
| `speculate-sound` | `(if g a r)` reaches what `r` reaches when `a` is equivalent to `r` unconditionally, for any guard value | L4.check.speculate, in its trivial form only: the implemented rules relate `a` to `r` under the guard (L4.check.speculate-assume, L4.check.speculate-value), which is not proved |

## The accounting calculus λ-acct

Accounts, exceptions and the affine judgment are formalized in a calculus
of their own (design/11-profiles.md), so that they do not touch the core
model's syntax or proofs: functions, `let`, `if`, tokens over one resource
(`take`, `spend`, `join`, `put`), deep handlers by operation name as in core
(multi-shot), `raise` and `try`. A configuration is a store (wallet, spent,
next id, live tokens as id and amount) and a term; a token in a term is a
reference `tok i` to a live entry. `ev` takes a flag: checked is Klara's
semantics (a token that is not live is the stuck state `reuse`), unchecked
is the step of code compiled with the check erased.

The judgment `Acct.HasTy G t A e` is simply typed (data, tokens, functions
with a latent effect flag) with two kinds of premise that make it affine:
a token variable occurs at most once on every path of its scope, and
function bodies, handler clauses and every part of a term that is still in
the context while another part may perform are token-free (L4.check.affine
clauses 2, 4 and 7). The invariant `Acct.Inv`: every token id occurs at most
once in the term, every id that occurs is live, and live ids are below the
next id.

| Theorem | Statement | Rules |
|---|---|---|
| `Acct.conservation` | every step of every term, typed or not, keeps wallet + spent + held in live tokens | L3.account.conservation (one resource, no jobs); copying a continuation cannot mint (L3.cont.context) |
| `Acct.preservation` | a typed configuration with the invariant steps to one | L4.check.affine (soundness) |
| `Acct.progress` | such a configuration is a value, steps, performs an unhandled effect, raises past every `try`, or is stuck, but never on reuse or a free variable | L3.affine.reuse |
| `Acct.no-reuse` | such a configuration never uses a token that is not live | L3.affine.reuse, L4.check.affine |
| `Acct.erasure`, `Acct.erasure-good` | on configurations with the invariant, the step with the reuse check erased is the step | L4.check.affine-erase |

The headline lemma is `Acct.ev-ok`: one evaluation of a typed term with the
invariant gives a step to a typed term related to it by `Acct.StepRel` (old
ids do not occur more, consumed ids occur no longer, new ids once), an
effect whose continuation and argument hold no token, a raised value
holding none, or a stuck state other than reuse. Not in λ-acct yet: several
resources, jobs and wallets per job, receipts, reads (`holds?`, `balance`),
`split`, recursion, and a check that the declared judgment (as implemented)
implies `HasTy`; the latter correspondence is stated in
design/11-profiles.md and tested by `test/klara/affine_test.clj`.

`test/klara/formal/acct_differential_test.clj` links λ-acct to Klara: it
generates token programs (with aliases, multi-shot handlers, raises and
catches) without regard to typing, runs them through the reader, expander
and CEK machine and through λ-acct's `step`, and requires the same outcome,
wallet and spent amount (500 programs by default; about a fifth end in
`L3.affine.reuse`).

### Workarounds to remove when ansatz catches up

The λ-acct proofs work around ansatz behaviour that differs from Lean 4
(listed for the ansatz maintainers in the Klara memory and fixed there one
pull request at a time). When Klara's ansatz pin is raised past those
fixes, remove:

- the `load-init!` guard at the top of `core.clj` and `acct.clj` (an
  idempotent `load-init!`);
- `Acct.ff-tt` (use `Bool.false_ne_true`) and `Acct.tf-subst0` (if `exact`
  accepts `j + 0` for `j`);
- the `show` steps that recover a function call after `unfold`, and the
  `cases q (e)` plus `dsimp only` detours, in `Acct.ev-val`, `Acct.if-ok`,
  `Acct.spendN-nv`, `Acct.spend-red`, `Acct.put-red`, `Acct.join-red`,
  `Acct.spendStep-erase`, `Acct.putStep-erase`, `Acct.joinN-erase` (once
  `simp only [f]` rewrites with f's equations only);
- the extra `cases h` after `simp at h` in `Acct.co-stepOut` and `Acct.tf-nil`
  (no-confusion in simp);
- `cases hb (Nat.beq ..)` in place of a named `by_cases` in
  `Acct.occ-substVar-ge`;
- the accessor lemmas (`Acct.rel-a` to `rel-e`, `Acct.inv-1` to `inv-3`,
  `Acct.ok-exn-v`, `Acct.ok-exn-c`, `Acct.lam-inv-b`, `Acct.lam-inv-l`) and
  the `Acct.*-ev` wrappers, where they only exist because `cases` renamed
  variables (keep those that read better);
- `exact` with every argument in place of `apply` (goal order), where
  `apply` reads better;
- `LE.le Nat instLENat` and `Bool.true`/`Bool.false` in the field types and
  indices of `Acct.Tf`, `Acct.HasTy`, `Acct.Inv`, `Acct.StepRel`, `Acct.OK`.

Not yet proved, though specified and tested (including adversarially,
`test/klara/adversarial_test.clj`):

- rewriting under binders (comparing function bodies needs contextual
  equivalence);
- the checker rules `L4.check.let-app`, `L4.check.speculate-assume`,
  `L4.check.speculate-value`, `L4.check.fix` (fixpoint induction),
  `L4.check.bool-let`, `L4.check.commute`, `L4.check.delta-data`,
  `L4.check.self`, `L4.check.const`, `L4.check.code`, `L4.check.alpha`, and
  the ownership judgment `L4.check.in-place` with its erasure theorem;
- the effect analysis (`L4.facts.effect`) and lowering (`L4.lower.*`);
- that the CEK machine refines `step` (tested differentially), and the
  bridge between named Core and `Tm` (tested).

## Proof-carrying candidates

When the definitional checker cannot relate a candidate to its reference,
a certificate may (L4.check.certificate). The certifier quotes the actual
reference and candidate terms with the bridge, states

```text
forall i : Int, inRange i -> forall terminal d, Star (ref i) d <-> Star (cand i) d
```

about exactly those terms, and checks the certificate's tactic proof with
the ansatz kernel. The assumption `inRange i` becomes a runtime guard: the
executable checks that its argument is a long and runs the reference
otherwise. `cases/certified_identity.clj` replaces `(* x 1)` by `x`, which
the definitional checker rightly rejects (it throws for non-numbers).

A certificate may carry `:range [lo hi]`: the theorem then also assumes
`lo <= i <= hi`, and the executable's guard is `[:range lo hi]`
(`cases/certified_horner.clj`; lemmas `prim-mul-ok`, `prim-add-ok`,
`in-range`, `reach-ev` in `checker.clj`).

Current limits: unary functions on integers. Proofs are written by hand
(the lemmas `equiv-of-reach`, `reach-beta`, `reach-prim` keep them short)
or searched by Klara programs in budgeted jobs (`klara.proof/certify`,
`cases/proof_search.clj`). Theorems as world definitions are next.

## The bridge

`bridge.clj` is trusted: it maps the expander's Core to `Tm` (de Bruijn
indices, curried functions, handler maps compiled to one dispatching clause)
and the implementation's results to observations. The differential test
runs the same source through the reader, expander and CEK machine, and
through the bridge and `step`, and requires equal observations for every
form inside the fragment.

It has already found disagreements that were real bugs:

- Clojure 1.12's boxed subtraction throws on `(- -4 Long/MIN_VALUE)`
  although the result fits; Klara now implements checked subtraction as
  specified (`klara.runtime.prims`).
- Applying `nil` raised a host `NullPointerException`; Klara now raises
  `L0.eval.not-fn`. The model gained keyword application.

## Notes on ansatz

Observed while porting from the earlier prototype (tag `prototype-2026-10-31`):

- Fixed since the prototype: `<` on `Int` now compiles; structural
  recursion with a varying non-matched argument is recognized (the old
  `substF`/level-in-result-type workarounds are gone).
- `(< i 0)` with `i : Int` elaborates the literal `0` as `Nat`; write
  `(Int.ofNat 0)` or compare with a named constant.
- Enum inductives are represented with `nil` for constructor 0 and the
  index for the others; other inductives use tagged vectors. The bridge
  depends on this.
- Redeclaring a constant is rejected, so iterating at the REPL means
  reloading the stack; `klara.formal.dev/load-forms!` skips declared forms.
