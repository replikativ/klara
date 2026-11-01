# Formal semantics

A kernel-checked specification of a fragment of Klara Core, written in
[ansatz](https://github.com/replikativ/ansatz) (the Lean 4 kernel in
Java, with a Clojure surface). The total function `step` is the
specification; ansatz compiles it to Clojure, so it is also an executable
reference interpreter.

```sh
clojure -M:formal:test-formal   # check every definition and theorem, run the differential tests
KLARA_DIFF_SEEDS=5000 clojure -M:formal:test-formal
```

## Files

| File | Content |
|---|---|
| `src/klara/formal/core.clj` | Syntax (`Tm`), worlds, checked 64-bit primitives, staging with generated names, `ev`, `step` |
| `src/klara/formal/ws.clj` | Well-scopedness: weakening, substitution, pinning, soundness of `run`'s closedness check |
| `src/klara/formal/props.clj` | Determinism, preservation, progress, safety, running quoted code |
| `src/klara/formal/checker.clj` | The checker's head rules are steps; a step preserves the terminal configurations reached |
| `src/klara/formal/certify.clj` | The ansatz certifier for proof-carrying candidates (L4.check.certificate) |
| `cases/certified_identity.clj` | A candidate admitted by proof: `(* x 1)` replaced by `x` for 64-bit integers |
| `src/klara/formal/bridge.clj` | The trusted bridge: quoting real Core terms into `Tm`, running the model, observations |
| `src/klara/formal/gen.clj` | A seeded generator of Klara programs inside the fragment |
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

| `beta-step`, `fix-step` | a call of a function on a value steps to the substituted body | L4.check.beta |
| `let-value-step` | a let of a value steps to the substituted body | L4.check.let-value |
| `if-true-step`, `if-false-step` | an if on a constant steps to the selected branch | L4.check.if-constant |
| `prim-step` | a primitive on constants steps to its result when it succeeds | L4.check.prim |
| `delta-step`, `pin-step` | a late or pinned global steps to its definition | L4.check.delta |
| `step-equiv` | a configuration and its step reach the same terminal configurations | composition |
| `speculate-sound` | `(if g a r)` reaches what `r` reaches when `a` does, for any guard value | L4.check.speculate |

Not yet proved: rewriting under binders (needs contextual equivalence),
`L4.check.let-app`, that the CEK machine refines `step` (tested
differentially), and the bridge between named Core and `Tm` (tested).

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

Current limits: unary functions on integers; the proof is written by hand
(the lemmas `equiv-of-reach`, `reach-beta`, `reach-prim` keep it short).
Proof search as a budgeted job and theorems as world definitions are next.

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
