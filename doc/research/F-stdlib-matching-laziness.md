# F. Standard-library abstractions, pattern matching, laziness, evaluation strategy

Research note for Klara iteration 1, 2026-10-27. It checks the five proposals
from the design conversation against our repositories, against primary sources,
and against black-box experiments on JVM Clojure 1.10.3, 1.11.4, 1.12.0 and
1.13.0-alpha6. Scripts and outputs are in
`/tmp/claude-1000/-home-christian-weilbach-Development-clojure/d015cfe9-5606-4419-ab30-07ea212bf22a/scratchpad/F/`
(`lazy.clj`, `lazy2.clj`, `fusion.clj`, with `.out` files). The clean-room
rule held: no `clojure/src/jvm/clojure/lang/*.java` was read. Status markers
are **Holds**, **Conj** and **Open**, as in `01-core-v1.md`.

## 1. Disagreements first

**F-D1. Rich Hickey's objection to pattern matching is not about performance
cliffs or implicit solving.** I found no statement from him against
unification or solving. In *Simple Made Easy* he puts rules and logic engines
on the *simple* side: "Conditionals are complex in interesting ways, and rules
can be simpler." His objection is about closedness, replication, positional
names, and coupling to representation. Verbatim, Clojure mailing list,
"keyword parameters?", 16 Jan 2008
(groups.google.com/d/msg/clojure/CqV6smX3R0o/3Xs_OEuHAQ0J):

> "If you are talking about the aspect of pattern matching that acts as a
> conditional based upon structure, I'm not a big fan. I feel about them the
> way I do about switch statements - they're brittle and inextensible. […]
> They are closed, enumerated in a single construct. They are frequently
> replicated. The binding aspect is used to rename structure components
> because the language throws the names away […] Certainly I'd want the
> binding part of pattern matching independent of the conditional part."

*Effective Programs* (Clojure/conj 2017, matthiasn/talk-transcripts,
slide at 00:45:23): "Having a de-, you know, a pattern matching of a
structural representation in a hundred places in your program is coupling,
right?" His only performance remark is from the same 2008 thread: "Without a
pattern-match optimizer, naive mechanical translation of patterns to if-else
constructs can produce slow code." Decision trees answer that one sentence.
They do not answer the main objection. The answer to the main objection has to
be **openness**: matching goes through open extractors and named keys, and
`defop`, not `match`, is the recommended mechanism for open dispatch.

**F-D2. "Decision trees, no backtracking" is a realization choice, not
semantics.** Maranget's decision trees never re-test a value, but their code
size can grow exponentially. Backtracking automata (Le Fessant and Maranget,
ICFP 2001) stay linear in size but may test a value more than once.
core.match already implements Maranget 2008 (`core.match/src/main/clojure/clojure/core/match.clj:21`).
By default it *backtracks via a preallocated exception* to limit code size, and
`*no-backtrack*` trades size for speed (`:79-89`). The semantics Klara must fix
is **first match, top to bottom, with pure extractors called an unspecified
number of times in an unspecified order**. Tree versus automaton is then a
per-site choice for the JIT.

**F-D3. Dispatching on the carrier is ill-posed for Monoid and Semilattice.**
One carrier has many monoids: numbers have `+`, `*`, `max` and `min`, and
maps have `merge-with f` for every `f`. Haskell's `Sum`/`Product` newtypes
are the scar this leaves. Clojure already chose the alternative: *the reducing
function is the monoid*. Its 0-arity gives the identity, its 2-arity the
operation, and its 1-arity the completion. This is dictionary passing, an
algebra as a value. Return-type polymorphism (`mempty`, `pure`) cannot work
under runtime dispatch on arguments at all, because there is no argument to
dispatch on. Recommendation: **an algebra is a value** whenever the structure
is not canonical for its carrier (Monoid, Join, Distance, Measure). Use
**`defop` on the carrier** only where one structure is canonical (`=`/`hash`,
default `compare`, extractors, `coll-reduce`).

**F-D4. Two citations in the proposal do not say what the proposal needs.**
(a) `doc/algebras.md` defines four *language-design* algebras: dispatch,
abstraction, syntax and semantics (`:1-16`). It is not a standard-library
algebra design, although its method fits: carrier, signature, laws,
falsifiers (`:3-16`). (b) The ESOP paper's algebra is a *commutative monoid
classified by how division works*, not a semilattice (`papers/esop27-joins/main.tex:193-213`,
Theorem "Product = join × shared part"). The idempotent case (c) is the
semilattice and needs no base. The cancellative case (b) needs the base.
Weights in (ℝ>0, ·), case (e), are the extreme where "no shared part can be
read off the states". Inference weights are exactly the PPL case, so a core
`Join` that is only a semilattice is wrong for Klara's flagship domain.
`Join` must declare a division class and take the base as an argument.

**F-D5. Value algebras and effect theories need different law machinery.**
Semigroup, Distance and Ordered are laws over carrier values, and
property-testing them means generating values. Measure (choose/observe/factor)
and fork/split are *equational theories over programs* (Plotkin–Power
algebraic effects). Checking them means generating programs and comparing
handler outputs, which are distributions. That needs exact enumeration under
the finite `H_meas`, or statistical tests with a stated false-pass rate. One
"property-tested" tier hides this difference.

**F-D6. "Laws license optimizations" mostly fails under Klara's defaults.**
- *Floating point*: `+` on doubles is not associative, so the most common PPL
  monoid, log-weight summation, fails the Monoid law. Reassociating a parallel
  fold is an **approximation permission** (`within ε`), not a law.
- *Laziness and effects*: map fusion is observable. Measured (`fusion.out`):
  for `(first (map g (map f (range 100))))` the unfused version calls `f` on
  32 elements and then `g` on 32; the fused version interleaves `f0 g0 f1 …`.
  When `g` throws at element 1, the unfused version has already performed
  **32** `f` effects and the fused version **2**. `(sequence (comp (map f) (map g)) …)`
  realizes 33 elements, not 32.
- *wandler's certificate covers a model, not Klara*: `List.map_map` is proved
  over Lean's finite, pure, total `List` (`wandler/docs/OPTIMIZER.md:43-58`).
  Nothing proves that Lean `List` refines a Clojure lazy seq with effects,
  chunking and infinite tails. Every fusion law needs side conditions (purity,
  totality, finiteness) that only effect information can discharge.
  wandler's assessment already says "Whole-model rewrites require stronger
  effect and trace laws" (`wandler/docs/ASSESSMENT.md:174`).

**F-D7. In JVM Clojure a lazy seq's realization cache is not an idempotent
memo, even for pure bodies.** Measured identically on 1.10.3, 1.11.4, 1.12.0
and 1.13.0-alpha6 (`lazy2-versions.out`):

| After the thunk throws once, a second read gives | |
|---|---|
| `(lazy-seq … (throw …))` | `NullPointerException`: the body re-runs with its closed-over locals nulled |
| chunked `(map f (range 5))`, `f` throws at 2 | `[]`: silently empty |
| unchunked `(map f (list …))` | `[0 1]`: silently truncated |
| `(delay … (throw …))` for comparison | the same exception, rethrown from cache |

This fits the `^:once` locals-clearing of the `lazy-seq` thunk, but that
mechanism is a hypothesis, not read from source. Two more falsifiers of
"pure ⇒ sharing unobservable":
- L5: a pure-looking body that allocates `(atom 0)` gives every consumer the
  *same* atom. The memo is idempotent only when the elements are values.
- L4: dynamic bindings are read at forcing time, so a 40-element seq forced
  partly inside a `binding` yields `{:bound 32, :root 8}`.

Klara's handlers have the same problem as bindings: a `perform` inside a lazy
body is interpreted by the handler active at forcing time.

**F-D8. Generators built from one-shot continuations are resources.** A lazy
seq whose tail is a captured one-shot continuation cannot be forced in two
forks. "Lazy seqs = yield effect + handler" therefore makes such seqs
non-forkable, unless the continuation captures no resources (then it is
multi-shot, and each fork re-runs it) or the realization is per world (§4.3).

**F-D9. partial-cps dual mode does not remove function colouring; it
monomorphizes both colours.** `async+sync` emits
`(if sync? <stripped body> (async body))` (`partial-cps/src/is/simm/partial_cps/async.cljc:138-170`),
so code doubles and the choice happens at run time. Closures are opaque:
`await` inside a `fn` literal is a compile error in both arms
(`ioc.clj:163-205`). `(map (fn [x] (await …)) xs)`, the higher-order case, is
exactly what it cannot do. Two smaller corrections:
- konserve does not use partial-cps. Its own `async+sync` is a postwalk
  translation table (`konserve/src/konserve/utils.cljc:112-128`, 95 call
  sites). datahike uses partial-cps (`datahike/src/datahike/index/persistent_set.cljc:9,146-156`).
- `partial-cps/…/sequence.cljc:2` excludes and redefines `first`, `rest`,
  `sequence`, `transduce`, `into` and `for` with async behaviour. That breaks
  our own naming rule.

**F-D10. Drop Functor, Traversable and Applicative from the core list.**
Direct-style effects subsume `traverse`: `(mapv f xs)` with `perform` inside
`f` *is* traverse in the handler's applicative. `pure` needs return-type
dispatch (F-D3). Clojure's `map` does not preserve the container, and under
our naming rule it must not start to. Keep **Reducible** (`coll-reduce`),
which Clojure already has.

## 2. What our repositories already have

| Asset | Where | Relevance |
|---|---|---|
| Algebra method (carrier/signature/laws/falsifiers), dispatch laws D-1..D-5 with redex probe | `lambda-join/doc/algebras.md:3-16, 43-76, 151-163` | template for every stdlib algebra |
| Sealed shapes with exhaustiveness at expansion, synthesized counterexamples, visible `:else` opt-out | `lambda-join/v0/src/v0/shape.clj:1-17, 33, 55` | exhaustiveness for sealed variants exists already (law A-4, `algebras.md:211-216`) |
| `defop` with fragments, conflict on same pattern | `v0/src/v0/dispatch.clj:145-160` | extractors register here |
| Clojure `for` (lazy + chunked) and `lazy-seq` family ported to v0 | `v0/src/v0/compat.clj:11-13` | hosted laziness exists |
| Colour vs capture analysis, Loom for one-shot, partial-cps for multi-shot | `algebras.md:475-590` | the async model is already argued; §4.4 refines it |
| ESOP join: commutative monoid by division class | `papers/esop27-joins/main.tex:193-230` | `Join` algebra |
| spindel delta algebras: monoid action with identity, homomorphism and associativity; Sequence is *partial* (size-indexed) | `spindel/docs/engine-formalism.md:106-160` | `Delta` algebra is a category action, not a monoid action |
| sci: lazy seqs rejected at forks; Delay forks as "pending realizations split, cached outcomes inherited" | `sci/doc/forking.md:99-101, 135`; `sci/doc/fork-state-audit.md:138-139, 341-348` | the fork rule for thunks already exists for Delay |
| **Untracked, in progress**: sci managed lazy seqs, "pending realization follows the consuming world", "realized prefix inherited with independent tails", "fork waits for an active realization", retry after failure | `simmis/.internal/worktrees/sci-managed-laziness/test/sci/lazy_seq_test.cljc:17, 39, 147, 231, 257` | this is the rule I recommend, already specified as tests |
| ansatz `match`: compiles to `casesOn`/`rec` by recursive case splitting | `ansatz/src/ansatz/surface/match.clj:1-30, 171-183, 499-558` | typed layer; **pitfall**: a bare symbol is a binder *unless it resolves to a constructor* (`:79-83`), the ML typo hazard |
| ansatz matcher metadata imported from Lean (`MatcherInfo`, overlaps) | `ansatz/src/ansatz/matchers.clj:1-12` | about 91% of Init matchers are non-overlapping: splitter = matcher |
| pangloss/pattern: SDF-style combinator matcher with success/fail continuations, segment variables `??`, rule combinators, nanopass | `pattern/src/pattern/matchers.clj:246-300, 1147`; `pattern/src/pattern/r3/combinators.clj:23-107` | backtracking rewriting; library, not core `match` |
| core.match: Maranget, open map patterns, `:only`, `:<<` views, multimethod extension points, no exhaustiveness check (throws "No matching clause") | `core.match/…/match.clj:21-33, 79-89, 147-156, 1542, 2061` | the existing Clojure answer, rarely used |
| wandler: certified fusion over Lean `List`, `Eq.trans` composition, strict kernel check | `wandler/docs/OPTIMIZER.md:20-60` | certified rewrites, model gap (F-D6) |
| partial-cps dual-mode law "sync ≡ async-all-warm" as a seeded generative suite (400 bodies: value, effect order, exception class) | `partial-cps/test/is/simm/partial_cps/equivalence_test.clj:1-10`; commit `ca386be` | the handler-equivalence obligation Klara needs |
| partial-cps async seqs `PAsyncSeq/anext` | `partial-cps/src/is/simm/partial_cps/sequence.cljc:8-40` | stream abstraction under a distinct protocol name |
| D note: `LazySeq` is a resource across forks unless beichte marks producers pure | `doc/klara/research/D-dispatch-interop.md:116-117, 143` | F-D7 refines it |

## 3. External survey (verified citations)

**GHC** (`../ghc`, all lines checked):
- *Laws are documentation.* Functor: `libraries/ghc-internal/src/GHC/Internal/Base.hs:948-952`.
  Monoid: `:643-647`. Foldable: `libraries/base/src/Data/Foldable.hs:979-1015`.
  Traversable naturality, identity and composition:
  `libraries/base/src/Data/Traversable.hs:1038-1059`.
- *RULES are unchecked*, `docs/users_guide/exts/rewrite_rules.rst:166-172`:
  "GHC makes absolutely no attempt to verify that the LHS and RHS of a rule
  have the same meaning … The responsibility is entirely the programmer's!"
  and "no attempt to make sure that the rules are confluent or terminating."
- *foldr/build* (Gill, Launchbury, Peyton Jones, FPCA 1993): `"fold/build"`
  at `GHC/Internal/Base.hs:1832`. The `map` rules need phase control to avoid
  an infinite loop (`:1902-1916`, `:1938-1940`). The `foldr/cons` rule is
  commented out because of "disastrously bloated code" (`:1843-1848`).
  Lesson: rule *orientation and staging* are part of correctness, which
  wandler's "each rule strictly removes a list" confluence argument addresses.
- *SpecConstr* (Peyton Jones, ICFP 2007): `compiler/GHC/Core/Opt/SpecConstr.hs:85-103`.
  Stream-fusion loops need forced specialization via a `SPEC` argument
  (`:459-483`). Worker/wrapper: `WorkWrap.hs:62`. Type-class specialization:
  `Specialise.hs:100-109`. Stream fusion itself (Coutts, Leshchinskiy,
  Stewart, ICFP 2007) lives in `text`/`vector`, not in this tree.
- *Coverage*: Lower Your Guards (Graf, Peyton Jones, Scott, ICFP 2020),
  `compiler/GHC/HsToCore/Pmc.hs:4-11`. View patterns become an opaque `let`
  (`Pmc/Desugar.hs:220-224`). Extractors are completed only by `COMPLETE`
  pragmas (`Pmc/Solver.hs:198-261`; `docs/users_guide/exts/pragmas.rst:1076-1084`:
  without one, "any pattern match on a pattern synonym is regarded as
  incomplete").

What to take from GHC: specialization on dictionaries and constructors, which
Klara reaches through `specialize` with guards; phase-ordered rules; and the
COMPLETE-set mechanism for extractors. What not to take: unchecked rules as
compiler input.

**Pattern matching.**
- Maranget, "Compiling pattern matching to good decision trees", ML Workshop 2008.
- Le Fessant and Maranget, "Optimizing pattern matching", ICFP 2001
  (backtracking automata).
- Wadler, "Views", POPL 1987.
- Emir, Odersky and Williams, "Matching objects with patterns", ECOOP 2007
  (Scala extractors, `unapply`).
- Syme, Neverov and Margetson, "Extensible pattern matching via a lightweight
  language extension", ICFP 2007 (F# active patterns).
- PEP 634/635/636 (Python 3.10). Mapping patterns ignore extra keys (open);
  class patterns map positions to attribute *names* via `__match_args__`.
  PEP 634 states that guards and extractors may be evaluated in an
  unspecified, implementation-dependent way, so side effects in them are not
  portable.
- Racket's `match` is extensible with match expanders. That is the
  syntax-extension route.

**Laziness, effects and streams.**
- Kiselyov, Biboudis, Palladinos and Smaragdakis, "Stream fusion, to
  completeness", POPL 2017 (strymonas: staged streams, no reliance on rules).
- Hickey, "Transducers are coming" (2014 blog). Transducers separate the
  process from the source; stateful transducers (`take`, `dedupe`) instantiate
  a volatile per reducing function, which is a resource.
- Kammar, Lindley and Oury, "Handlers in action", ICFP 2013 (generators as
  handlers).
- Sivaramakrishnan et al., "Retrofitting effect handlers onto OCaml",
  PLDI 2021 (one-shot by design).
- Xie and Leijen, "Generalized evidence passing for effect handlers",
  ICFP 2021.

**Metrics and approximation.**
- Reed and Pierce, "Distance makes the types grow stronger", ICFP 2010
  (Fuzz: sensitivity types, so ε propagates through Lipschitz maps).
- Mathlib classes to reuse:
  - `SemilatticeSup`: `mathlib4/Mathlib/Order/Lattice.lean:67`
  - `CommMonoid`: `Mathlib/Algebra/Group/Defs.lean:805`
  - `MulAction`: `Mathlib/Algebra/Group/Action/Defs.lean:135`
  - `PseudoMetricSpace` / `MetricSpace`: `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:141`, `Defs.lean:70`
  - `LinearOrder`: `Mathlib/Order/Defs/LinearOrder.lean:61`
  - `Measure`: `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:77`
- KL divergence is neither symmetric nor triangle-satisfying. It is the
  quantity VI actually controls (Pinsker bounds TV by √(KL/2)).

## 4. Recommendations for Klara v1

### 4.1 Algebras

Representation: an algebra is a map-like value `{:op … :id … :laws #{…} :grade …}`,
passed explicitly or selected by a named default. Carrier dispatch through
`defop` is reserved for the starred rows (canonical structure). Each law
carries a grade: **G0** documented, **G1** property-tested (default; generators
per instance, run in the corpus), **G1ε** property-tested up to a declared ε
(floats), **G2** proved in ansatz against the Mathlib class. Side conditions
(purity, totality, finiteness) are part of the law and are discharged by
effect information, not by testing.

| # | Algebra | Laws | Klara feature that needs it |
|---|---|---|---|
| 1* | **Equiv/Hash** (`=`, `hash`) | equivalence; `a = b ⇒ hash a = hash b`; layout-independence | representation freedom (Core §2), caches, content identity |
| 2* | **Ordered** (`compare`) | total preorder consistent with `=`; NaN excluded or ordered by a declared total order | sorted collections, `sort`, `Ordered`-licensed binary search |
| 3 | **Monoid** (the reducing fn: 0-, 2- and 1-arity) | associativity, identity; `commutative?` flag | `reduce`/`fold`; parallel `fold` only if commutative and G1/G2, otherwise `within ε` |
| 4 | **Join** = commutative monoid + division class `:idempotent \| :cancellative \| :free \| :none` + `(join base x1 x2)` | ESOP Thm (a)–(e); semilattice ⇔ `:idempotent` (base ignored) | `fork`/`join`, G13, CRDT-style merge, evidence pooling (G1) |
| 5 | **Delta** = partial monoid *action* (a category acting on states) | `apply(t,id)=t`; `apply(t,d₁·d₂)=apply(apply(t,d₁),d₂)`; compose defined only on compatible pairs | spindel incremental views, yggdrasil merge deltas, re-specialization diffs |
| 6* | **Reducible** (`coll-reduce`, `reduced`) | reduce = left fold in seq order; `reduced` short-circuits; finite or `reduced`-terminating | every collection, transducers |
| 7 | **Transducer** (value `rf → rf`) | composition = `comp`; completion called exactly once; instantiated stateful rf is a **resource** | the recommended pipeline (§4.4) |
| 8 | **Distance** with kind `:metric \| :pseudometric \| :divergence` | metric axioms only for `:metric`; triangle-based ε composition only for `:metric`; plus a **Lipschitz** declaration per op (Fuzz) | `within ε` (G3), `translate` error models, `converge` residual bounds |
| 9 | **Measure** (effect theory: choose/observe/factor) | bind associativity; commutativity of independent `choose` (Staton); `factor` is the monoid (ℝ≥0, ·); `observe` = `factor` ∘ density | `H_meas`, inference handlers are tested against it |
| 10 | **Split** (effect theory: key and evidence split) | split determinism; split-then-join conserves mass for evidence; key-split independence as a *statistical contract* | Q6, G1, G9 |
| 11 | **Grade/Budget** (partially ordered commutative monoids; sequential `+`, parallel `max`) | ordered-monoid laws; hard vs traded components | ledger, G8 |
| 12* | **Seq** (`seq`/`first`/`rest`) | `(seq (seq x)) = (seq x)`; `(first (cons a s)) = a`; realization at most once per world (§4.3) | laziness, interop |
| 13* | **Extractor** (for `match`) | pure; total or returns a no-match sentinel; optional `COMPLETE` set | `match` (§4.2) |

Thirteen algebras, four of them already Clojure protocols (1, 2, 6, 12). Not
in v1: Functor, Applicative, Traversable, Monad (F-D10), and a lattice tower.
Laws license compiler rewrites **only at G2**, or at G1 for rewrites the
*instance owner* opts into with blame on that owner (the Haskell Monoid
convention, made explicit).

### 4.2 `match`

- **Semantics**: first match, clauses top to bottom. Defined by a naive
  reference interpreter in the spec. Compiled code must agree with the
  interpreter whenever the extractors are pure.
- **Binders vs tags**: a bare symbol always binds. Tags are keywords or
  explicitly marked constructor heads, never "binds unless it resolves" (the
  ansatz/ML hazard, `match.clj:79-83`).
- **Map patterns are open by key, with exactly destructuring's semantics**
  where the syntax overlaps (same name ⇒ same behaviour). `:only` closes a map
  pattern, as in core.match.
- **Vector patterns are exact-length, with `& rest`.** Seq patterns force at
  most *n+1* elements, a laziness bound stated in the spec.
- **Extractor patterns** `(op args… :as p)`: an `op` registered with a declared
  `:extractor` fragment, so it is open, owned, and extensible by others. This
  is Rich's openness requirement. Positional sugar for records maps positions
  to *names* through the record's declared field order, as `__match_args__`
  does, so names are never thrown away.
- **Guards**: `:when`. They are pure, with the same unspecified-evaluation rule.
- **Exhaustiveness only for sealed shapes**, using `v0.shape`'s counterexample
  synthesis. Extractors count only when declared in a `COMPLETE` set. Open
  matches throw a named `:match/no-clause` error.
- **Compilation**: Maranget's heuristics under a code-size budget, falling
  back to a backtracking automaton. Which one is used is a per-site
  realization choice, with no semantic difference.
- **Scope**: `match` is a syntax extension (Core §13) elaborating to
  `if`/`let`/`prim` plus extractor calls. No unification, no segment
  variables. pangloss/pattern-style rules (segments, backtracking) ship as a
  *library* for syntax extensions and wandler rule authoring, where search is
  the point.
- **Positioning lint**: a `match` with more than *k* tag clauses over an
  unsealed tag set suggests `defop`. This answers "frequently replicated".

### 4.3 The laziness rule

A lazy seq is three things: a realized prefix (data), a pending thunk
(control), and a lock (synchronization). The rule addresses each part.

1. **The realized prefix is shared across forks iff its elements are values**
   (sort check at fork, cached per cell).
2. **The pending thunk is split at a fork. Each world realizes its own tail
   under its own world, bindings and handlers.** This is sci's Delay rule
   (`fork-state-audit.md:138`) and the sci-managed-laziness test contract. A
   fork during an active realization waits for it to finish
   (`lazy_seq_test.cljc:257`). For pure bodies this is unobservable. For
   world-local effects it behaves like two sequential programs. **No purity
   assumption is needed for hosted Klara seqs.**
3. **Realization runs at most once per world.** JVM Clojure already runs it
   once across 8 racing threads (`lazy.out` L1). Klara keeps that per world.
4. **Failure is cached and rethrown, as Delay does.** Klara does not re-run
   the thunk with cleared locals (F-D7). This differs from JVM Clojure only
   on a path that currently returns garbage. Q2 asks whether this needs a new
   name.
5. **Irreversible host effects make a seq a resource** (`line-seq`, network
   streams). A fork over such a seq is rejected with "realize or `vec` before
   fork".
6. **Linked Clojure `LazySeq` objects** have one host cache and cannot be
   split. Accept them at a fork only if the producer is classified pure
   (beichte) *and* the realized elements are values; otherwise reject. This
   replaces G7's blanket Tier H trust, which L5 falsifies.
7. **Bindings and handlers apply at forcing time** (same behaviour as
   Clojure). `bound-fn` keeps its meaning. `perform` inside a lazy body gets a
   lint, and effectful producers should use streams (§4.4).
8. **Chunking keeps Clojure's 32-element effect timing** as a Tier M law
   (`lazy.out` L3: `range`/vector 32, list/`iterate`/`(range)` 1).
9. **Holding the head**: a world snapshot or receipt that captures a seq head
   pins memory (`lazy.out` L8: 31 MB held vs 0). Fork snapshots must not
   capture locals beyond what the continuation needs. This is an obligation
   on the continuation representation.
10. **A self-forcing thunk is a named cycle error**, not a `StackOverflowError`
    (`lazy2.out`).

### 4.4 Evaluation strategy and async

- **Effects with one-shot continuations are the model; `await` is a
  `perform`.** Source code carries no colour.
- **Realization per host**:
  - *JVM*: Loom virtual threads for one-shot suspension. Loom captures *host
    frames*, so Klara → linked Clojure → Klara callback → `await` works.
    Neither CPS nor partial-cps can capture that path (F-D9).
  - *Multi-shot* (`branch`, SMC, backtracking): selective CPS in regions that
    contain no host frames. A multi-shot capture through a host frame is a
    tested boundary error.
  - *JS/cljs*: partial-cps-style CPS, with Klara's own hosted higher-order
    functions compiled effect-polymorphically. Linked `clojure.core/map`
    cannot carry an `await`.
- **The dual-mode law becomes a handler obligation**: a direct handler and a
  suspending handler must agree whenever nothing suspends (value, effect
  order, exception class). Lift partial-cps's generative suite
  (`equivalence_test.clj`) into the conformance corpus. Two-arm compilation is
  `specialize` on the handler stack (`algebras.md:543-566`), not a macro.
- **Names**:
  - `map`, `filter` and `for` stay lazy and chunked.
  - Strict and fusing pipelines use names Clojure already has: transducers via
    `into`, `transduce`, `eduction` and `sequence` (which differ observably;
    `eduction` re-runs per reduction: 20 vs 10 calls in `lazy2.out`).
  - Streams (pull-based, effectful, resource-sorted) get distinct names:
    `stream`, `snext`, `yield`. Rename partial-cps's shadowed `for`,
    `sequence` and `into` before Klara adopts them.
- **Generators**: a `yield` handler produces a **stream**, never a lazy seq
  (F-D8). Converting with `(seq-of stream)` realizes per world and marks the
  result a resource if the source is irreversible.

### 4.5 Producer/consumer adaptation

- Rewrite rules are world values with an orientation, a phase, side conditions
  and a law grade.
- A rule enters the optimizer only with a G2 certificate (wandler) *for the
  Klara-level semantics*. Until the Lean `List` to lazy-seq refinement is
  proved, certified fusion applies only to producers that are **finite, strict
  and pure** (vectors and transducer pipelines over reducibles).
- Representation negotiation, dispatch on (producer-rep, consumer-rep), is a
  `defop :multiple` whose extensions are certified specializations
  (algebras.md §1.4 rung 1). JIT-observed types drive which specializations
  are built, never which ones are legal. This is GHC's SpecConstr and
  Specialise moved to run time with guards.

## 5. Obligations and falsifiers

| # | Claim | Status | Falsifier |
|---|---|---|---|
| F1 | JVM LazySeq realization runs once under concurrent forcing | **Holds** (measured, 3×8 threads) | any trial with >1 body run |
| F2 | Pure lazy seq cache is an idempotent memo in JVM Clojure | **Refuted** (F-D7, 4 versions) | — |
| F3 | Per-world thunk split + inherited value prefix makes pure realization unobservable across forks | **Conj** (sci tests specify it) | a pure program whose result depends on fork-vs-realization order |
| F4 | Map fusion is sound for pure total `f`, `g` over finite or lazy seqs | **Conj** (G2 for `List`, refinement Open) | an effect-free counterexample involving chunking or `reduced` |
| F5 | Map fusion is sound for effectful `f`, `g` | **Refuted** (`fusion.out`: 32 vs 2 effects) | — |
| F6 | Monoid laws hold for doubles | **Refuted** (associativity) | — |
| F7 | Decision-tree match = naive first-match for pure extractors | **Conj** (Maranget; core.match) | differential test failure |
| F8 | Maranget trees stay within 2× the size of the backtracking automaton on the corpus | **Open** | blowup on realistic syntax-extension grammars |
| F9 | Carrier-dispatched Monoid is unambiguous for stdlib types | **Refuted** for numbers and maps (F-D3) | — |
| F10 | Effect-theory laws (Measure) are checkable by exact enumeration in v1 | **Conj** for finite discrete `H_meas` | recursion with unbounded support (critic §1) |
| F11 | Loom carries one-shot `await` through linked Clojure frames | **Conj** | a pinned-carrier or `synchronized` deadlock in `clojure.core` paths (LazySeq locks) |
| F12 | Direct and suspending handlers agree when nothing suspends | **Holds** for partial-cps's grammar (400 bodies) | any body outside the grammar, e.g. a closure |
| F13 | Rich's objection is answered by openness, not by decision trees | **Conj** | Clojure users still reject `match` once it is extractor-based and map-open |

## 6. The smallest experiments

1. **X-F1 Lazy-fork contract on v0** (about 2 days). Port the 16
   sci-managed-laziness tests to hosted v0 seqs and add F-D7's failure cases.
   *Decides* rules 1–4. *Kill*: per-world split costs more than 1.2× on a
   non-forking `(reduce + (map inc (range 1e7)))`.
2. **X-F2 Match differential** (about 3 days). Build a Maranget compiler
   behind a naive interpreter and run test.check over random sealed shapes,
   map patterns and extractors. Compare code size and speed against core.match
   and `case`. *Kill for "trees by default"*: median code size more than 3×
   the automaton.
3. **X-F3 Algebra-as-value vs carrier dispatch** (1 day). Implement Monoid,
   Join, Distance and Ordered for numbers, maps, vectors, distributions and
   weights in both styles. Count ambiguous or missing instances and call
   overhead.
4. **X-F4 Purity-guarded fusion** (2 days). Generate 1000 pipelines with
   effectful and pure stages. Fuse only stages marked pure by beichte, then
   compare effect traces with the unfused pipeline. *Pass*: zero trace
   differences with the guard, and nonzero without it (reproducing F5).
5. **X-F5 Loom vs CPS through linked callbacks** (2 days). Run `await` inside
   `clojure.core/map`'s fn and inside `reduce`, plus SMC multi-shot over a
   CPS region. Measure allocations per capture and check for carrier pinning
   on LazySeq locks.
6. **X-F6 ε-laws** (half a day). Property-test Monoid associativity on doubles
   and Kahan-compensated sums with declared ε. Settle what G1ε means
   (absolute, relative, ULP).

## 7. Questions for Christian

1. **Algebras as values or by dispatch?** I recommend values for Monoid, Join,
   Distance and Measure, and `defop` only for canonical structure (F-D3).
   Do you accept losing `(fold xs)` without naming the monoid?
2. **Failure caching in `lazy-seq`.** Klara would rethrow the cached
   exception (Delay semantics); JVM Clojure re-runs with cleared locals and
   returns truncated data. Is this divergence acceptable under the same name,
   given that the Clojure behaviour is unspecified and broken, or does it need
   a new name?
3. **Who may license an optimization?** G2 only (wandler), or also G1 laws with
   blame on the instance owner, the way Haskell libraries assume Monoid laws?
4. **Is `Join` with a division class the right core for G13?** Or should
   weights always be computed in a free presentation and interpreted
   afterwards (ESOP Thm (d))?
5. **For `within ε` on distributions, which `:divergence` is the default:
   KL, TV or Wasserstein?** Only metrics compose by the triangle inequality.
6. **Should `match` exist in v1 at all**, or only `shape-case` plus
   destructuring plus `defop` extractors, with `match` deferred until X-F2
   reports?
