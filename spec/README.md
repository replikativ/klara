# Klara Core: executable small-step specification (S2 / X3)

This is a kernel-checked small-step operational semantics for Klara Core, written in
[ansatz](../../ansatz), the Lean 4 kernel and elaborator reimplemented in Clojure. The
total `step` function is the spec. Compiled to Clojure by ansatz, the same function is
also the reference interpreter. This follows research note A §4, "Spec structure" (1)–(2).

```
clojure -M:test        # kernel-checks every definition and proof, then runs the 26 test programs
clojure -M:repl        # nREPL on port 7891
```

**Requires ansatz at or after `08bfad4`** (origin/main, 2026-10-27). `deps.edn` points at
`../../ansatz` through `:local/root`. When that checkout is older, override it, for example
`clojure -Sdeps '{:aliases {:m {:override-deps {org.replikativ/ansatz {:local/root "<ansatz@08bfad4>"}}}}}' -M:test:m`.
The whole development was checked against `08bfad4`. Everything except `WSC` and the
config-level corollaries also checks on `ffe045d`. A full check takes about 45 s on a
warm JVM.

## What is formalized

| File | Content |
|---|---|
| `src/klara/spec/core.clj` | Syntax, values, substitution, primitives, `run1`, `step` |
| `src/klara/spec/ws.clj` | `WS n t` (well-scopedness): weakening, substitution lemma, closed substitution is the identity |
| `src/klara/spec/props.clj` | `Step` and `Star`, the outcome invariant `OK`, determinism, preservation, progress, safety, s-m-n |
| `src/klara/spec/interp.clj` | Unverified bridge: named EDN surface → de Bruijn `Tm`, a driver loop, and observation of the result |
| `test/klara/spec/programs.edn` | 26 programs as data, each with its expected observation |

**Syntax.** `Tm` is a de Bruijn inductive with the 12 forms: `var` (local), `lit` (quote of
a datum: nil, Bool or Int), `lam`, `app`, `let_`, `if_`, `letrec`, `resolve`, `prim` (`+ - * = <`),
`perform`, `handle` and `specialize`. Three more forms are runtime-only, in the style of
Wasm's administrative instructions: `fix` (the recursive closure), `cap l` (the capability of
handler instance `l`) and `handling l b r o` (an installed instance). Functions are unary and
application is binary; the front end curries `(fn [x y] e)` and `(f a b)`.

**Semantics.** `run1 : World → Nat → Tm → Out` is structural, CBV and left-to-right. The
`Out` of a term is one of:
- `val`: the term is a value;
- `next n e`: the term steps to `e`;
- `eff tg op v k`: the term is `E[perform tg op v]`, `E` does not handle `tg`, and `k = E[var 0]`;
- `stuck s`: a named stuck state.

Evaluation contexts are reified: each frame extends the captured `k` as an effect
bubbles outward (`frame`, `seq1`, `seq2`).

`step : Config → Option Config` is total. `Config = (world, fresh-label counter, term)`.
`Step` is its graph, an inductive relation with one constructor.

**Handlers (v2 §1: lexical handler instances, deep).** `(handle b r o)` allocates a fresh
label `l`, substitutes `cap l` for the handler variable in `b`, and installs
`handling l …`. A `perform` names its target. When the target evaluates to `cap l`, the
effect is caught only by `handling l`, never by an inner instance; the program
`:lexical-targeting` tests exactly this. The op clause binds the op tag, the argument
and `k' = (fn [y] (handling l k[y] r o))`. That reinstalls the instance, so handlers are
deep and resumption is multi-shot in the reference semantics (`:multi-shot`). The front
end turns a `{:op clause …}` map into one clause that dispatches on the op tag.

**Ambient effects** are modelled minimally:
- `resolve id` reads a finite map (`World`, an association list) held in the configuration;
- `(perform nil op v)` is an ambient op, and nothing handles it in Core, so at top level it
  is the named stuck state "unhandled op";
- a capability that escapes its instance and is then performed on is the named stuck state
  "unhandled instance".

The other named stuck states are `notFn`, `primType`, `badTarget` and `unbound id`.
`scope`, meaning a free variable reached evaluation, is the only unnamed failure.

**specialize.** It has its reference meaning: `(specialize p m)` with `p` and `m` values
steps to `(fn [y] (p m y))`.

## Proof status

| # | Statement | Status | Where |
|---|---|---|---|
| (a) | Determinism: `Step c c1 → Step c c2 → c1 = c2` | **Holds** | `props/step-det` |
| (c) | Preservation of well-scopedness: `Step c c2 → WSC c → WSC c2` (closed world and closed term) | **Holds** | `props/preservation`, `preservation-config` |
| (b) | Progress modulo named stuck states: `WSC c → Progress c`. A closed config is a value (`isVal`), steps, is an unhandled effect (ambient op or escaped capability), or is a named error ≠ `scope` | **Holds** | `props/progress`, `progress-config` |
| (b+c) | Safety: `WSC c → Star c c2 → Progress c2` | **Holds** | `props/safety` |
| (d) | s-m-n for the trivial specializer: for closed values p, m, x, `((specialize p m) x) →→ (p m x)` (two steps). Step equivalence follows: both sides reach the same terminal configurations | **Holds** | `props/smn`, `smn-equiv` |
| | s-m-n for a non-value argument | **Open**, and false as an equation | `((specialize p m) e)` runs `e`'s effects before `(p m)`'s; `(p m e)` runs them after. The law holds at values, which is the data reading of MC I eq. 12 |
| | `run1 t = val ↔ isVal t` | **Holds** | `run1-val`, `isVal-run1` |
| | Uniqueness of labels / that `cap l` targets exactly its own instance | **Open** | not stated; the fresh counter is monotone by construction |
| | Adequacy, A-O3 injectivity of code identity, the authority/resource discipline (A-O4) | out of scope | |

**What progress means for a total step function.** Because `step` is total, "value or steps
or stuck" holds trivially. The content of (b) is narrower: (1) closed terms never produce
`scope`; (2) the `val` outcome coincides with the syntactic value predicate; and
(3) every other outcome is an explicitly named state. The real induction is
`props/run1-ok`. It proves one outcome invariant `OK (run1 w n t)` for `WS 0 t` and a closed
world, which says:
- every `next` term is closed;
- every effect carries a closed argument and a context that is closed except for its hole;
- every stuck state is not `scope`.

That one induction carries both (b) and (c).

**Effort and the kill rule.** Wall-clock time, including discovering the ansatz
workarounds listed below:
- (a): 10 min.
- Substitution lemma and weakening: about 40 min. Most of it went on the var case and
  ansatz tactic behaviour.
- The outcome invariant and (c): about 60 min.
- (b): about 45 min, interrupted by two session restarts.
- (d) with closed-substitution identity: about 30 min.
- Config-level corollaries and safety on the new ansatz: 15 min.

That is about 3.5 h in total for 53 theorems in ≈550 lines (ws + props). `Core.lean`'s
preservation, progress and substitution take ≈420 lines. The kill rule (more than 2× the
effort of the corresponding Core.lean proofs) was **not triggered**. The comparison is
weak in one direction: well-scopedness is a simpler invariant than Core.lean's footprint
typing. It is weak in the other direction too: this calculus has 15 constructors against
7, plus effects and contexts. The first typed invariant (authority/footprint, A-O4) is the
real test of ansatz as the host.

## Running it: the compiled interpreter

`klara.spec.interp/run` iterates the compiled `step`, for example
`(run '(handle [h] (prim + 1 (perform h :get nil)) {:get (fn [v k] (k 41))}))` →
`{:value 42 :steps 9}`. Each program in `test/klara/spec/programs.edn` is EDN with
`:program`, an optional `:world` and `:expect`. All 26 agree with expectation:
- arithmetic and negative ints;
- Clojure truthiness;
- letrec loops (`fact 20`, `sum 100`);
- world reads;
- tail-resumptive, abortive, deep, multi-shot and state handlers;
- lexical targeting;
- ambient and escaped-capability stuck states;
- specialize;
- the type-error stuck states.

These programs are meant to run differentially against the T0 interpreter in `klara/src`.
The observation format is `{:value v}` or `{:stuck kind …}`; closures observe as
`:klara/fn`. The runtime representation that `interp.clj` builds (tagged vectors, enum
nil/index, `Option` as nil/`[x]`) is ansatz's current codegen representation. It is
documented at the top of that file and will need adjusting if ansatz changes it.

Each step costs O(term size): `run1` re-traverses the term and eagerly computes the `done`
outcomes. `fact 20` takes 104 steps and finishes instantly. This is fine for a reference
oracle, not for the corpus at scale.

## ansatz features used

- `a/inductive`: plain inductives; indexed `Prop` families (`WS`, `WSW`, `WSC`, `OK`,
  `Step`, `Star`, `Progress`).
- `a/defn`: structural recursion; nested `match` with wildcards; function-valued results
  and arguments (`substF`, the frame functions); compilation to Clojure.
- `a/theorem` tactics: `induction`, `cases` (including `cases h e` and `:with`), `simp`,
  `simp … at`, `simp_all`, `split`, `split_ifs`, `omega`, `grind`, `constructor`, `apply`,
  `exact` (with `_` holes), `rw … at`, `revert`, `have`, `obtain`, `first`, `try`,
  `all_goals`, `and_then`.
- Bundled Init only (`a/load-init!`); no Mathlib.

## Lean-4 compatibility notes

The shape is Lean's: plain inductives, structural recursion, `Prop` relations and
tactic proofs written so they could be transliterated. Where the code differs because
of ansatz:

1. **`substF v t : Nat → Tm` instead of `subst j v t`.** ansatz recognises structural
   recursion only when non-matched arguments are unchanged, so the varying index moved into
   the result type. Lean would write `subst (j : Nat) (v : Tm) : Tm → Tm`.
2. **Recursive results are passed to `seq1`, `seq2` and `handlingOut`**, never matched on
   directly. ansatz does not see `match (run1 w n f) …` as structural.
3. **Index comparisons are `match (Nat.beq i j) …`** rather than `if i = j`. When this was
   written, `split` did not reduce `ite`. That is fixed in `dbc7186`, so they could go back
   to `if`. They are kept because the Bool form is equally valid Lean and the proofs are
   stable.
4. **`intLt`** goes through `Int.natAbs` (see item 4 under "Blockers" below). Lean:
   `decide (i < k)`.
5. **`primResult` and `resolveResult`** are separate functions so that a `match` on an
   `Option` result can be case-split. Lean's `split` would do this inline.
6. **Some lemmas take `revert`-then-`apply` form, or exist only to name a case**
   (`ws-substF-var`, the `progress-*` helpers), because of inaccessible names and apply
   unification. These were fixed upstream (`dbc7186`: apply holes, `assumption` with
   metavariables, `rename_i`) but not yet simplified here.

The `ansatz.surface.lean` emitter was **not tried** on this development, so F9
("Lean re-checks it") stays **Conj**. A hand port is mechanical given the notes above.

## Blockers and ansatz reports

I sent these reports to the ansatz session (`ansatz-12`). Its triage, and the state at
`08bfad4`:

| # | Report | Triage | State at 08bfad4 |
|---|---|---|---|
| 1 | A single-constructor Prop family indexed by a constructor application of its fields fails recursor generation (`generated recursor type mismatch`) | fix: Lean's elim_only_at_universe_zero | **Fixed** (55f52be). `WSC` is now used |
| 2 | Structural recursion is not detected when a non-matched argument varies | Lean brecOn structural recursion, match-compiler stage 4 | **Open**. Workaround `substF` kept |
| 3 | A recursive call as a `match` scrutinee is not structural | same, stage 4 | **Open**. Workaround helpers kept |
| 4 | Int `==`/`<` codegen; Int `match` miscompiles; Bool `==` → Nat.beq; constant half-admitted after a codegen failure | queued behind the DecidableEq rework | `==` on Int and on Bool: **fixed** (72bd88d), workarounds removed. `<` on Int: **open** ("Int.decLt has no Clojure runtime lowering"). Int `match`: **open** ("nth not supported on this type: Long") |
| 5 | `split` leaves `ite`; `rw [if_pos h]` universe metavariables; `split_ifs` only on Bool.rec; apply with `_`; `assumption` with metavariables; `rename_i`; `generalizing` order | fix as one task | **Fixed** (dbc7186). I checked that `split` now reduces `ite`. Proof simplifications not yet applied |
| 6 | Nested matches with wildcards in two arms: "Equation generation failed … `_match_1` already declared" (`datumEq`, `primApply`) | stage 3 (MatchEqs) replaces it | **Open**. It only prints warnings, and nothing here needs those equations |

The coordinator mentioned an outstanding ansatz task T37. I don't know which report it
tracks. Nothing open blocks this development; items 2, 3, 4 (Int `<`, Int `match`) and 6
only force the workarounds above.

## Next steps

- Make the step relation rule-based (paper-style evaluation-context rules) and prove it
  equal to the graph of `step`. That gives the readable rule table A §4 asks for.
- Uniqueness of labels, then a theorem that a capability's effect is handled by its own
  instance.
- Port Core.lean's footprint typing onto this syntax: the first slice of A-O4, and the
  real test of the kill rule.
- Run `programs.edn` against T0 (`klara/src`, S1), and then against the v0 corpus.
