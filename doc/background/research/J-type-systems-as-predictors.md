# J. Type systems as predictors over Klara's AST

Research note, Klara iteration 1, 2026-10-27. It builds on `01-core-v2.md`
(§1–3, §7), `05-architecture.md` §9 (the predictor ladder), research notes
C, D, F and G, RFC 0001/0002, and the studies `lambda-join/studies/{scala,
typedclojure,elixir-types,koka}.md`. Code was read at these heads: scala3
`4a31256a04` (2026-03-24), typedclojure `integration` plus branch
`feature/memory-analysis` `87d87c881` (read via `git show`), koka `b7637b3`,
elixir `bc7844c`, ansatz `01016b2`, and beichte at its working tree. One
black-box probe was run on beichte, as described in §2.4. No repository was
modified. Status markers: **Holds**, **Conj**, **Open**, **Refuted**.

## 1. Disagreements first

**J-D1. "Type systems are level 0, about free at compile time" holds for half
of the list.** Shapes with occurrence typing, effect rows, capture sets and
0/1/ω usage infer in roughly linear time per definition. Liquid types call an
SMT solver for each subtyping constraint. Dependent proofs in ansatz cost
human time. Even the cheap systems have scars: Elixir caps inference at 16
clauses (`elixir/lib/elixir/lib/module/types/apply.ex:16`) and turned
inference off for tests (studies/elixir-types.md §5). I propose splitting
level 0 into **0a** (cheap, always on, inferred) and **0b** (SMT or proof,
scheduled by value of computation like levels 1–3). Both are sound. Only
their cost differs, so only their scheduling differs.

**J-D2. "A sound static fact is guard-free" is false in a redefinable
world.** A fact about `f` that used the summary of `g` holds only for bases
in which `g` has that summary. Klara has three kinds of fact, and they need
different machinery:

- *Closed* facts are about one definition's own AST. They are truly
  guard-free.
- *Basis* facts read other definitions. They need no runtime guard, but a
  publication must invalidate them on the writer side, like a var protector.
  An executable pinned to the old basis stays valid (R4).
- *Host* facts come from Tier H oracles: reflection, the annotation corpus,
  linked code. They are never certificates. They are guarded or trusted, and
  the receipt says which.

Research note C already has the right algebra: a fact's grade is its
assumption set, `S ⊑ A ⊑ D` (C-staging.md:22-29, 262-274). §4 uses it.

**J-D3. Scala 3's capture checker is a checker, not a predictor.** Klara
should take its domain, not its architecture.
- `CheckCaptures` is a `Recheck` phase (`scala3/compiler/src/dotty/tools/dotc/cc/CheckCaptures.scala:236`).
- `Recheck` keeps its new types only when `-Vprint:cc` is set
  (`transform/Recheck.scala:205-210, 666-668`). Otherwise they are
  discarded.
- It runs after TASTy pickling (`Compiler.scala:50` vs `:87-88`), so inferred
  capture sets never reach the typed-tree store. TASTy records only that the
  file was capture-checked (`CAPTURECHECKEDattr`,
  `tasty/src/dotty/tools/tasty/TastyFormat.scala:286, 641`).
- The one runtime payoff people credit to capabilities is
  `boundary`/`break` becoming jumps. That comes from `DropBreaks`, a
  syntactic phase that needs no capture types: it requires the same method
  and no intervening `try` (`transform/DropBreaks.scala:35-41`).

Klara wants the reverse: keep every inferred fact as evidence, persist it,
and let the specializer consume it.

**J-D4. "Effect absence" is the wrong unit; the decisive prediction is the
absence of an operation class, plus latent effects.**
- **Koka's selective monadic translation turns on operation classes.** It
  keeps an application in direct style unless its effect row has an open
  tail or contains an operation declared `ResumeMany`
  (`koka/src/Core/Core.hs:872-878`, used at `src/Core/Monadic.hs:132`).
  Effects that are present but tail-resumptive or abortive cost no CPS.
  That matches Klara's per-definition classification (v2 §4).
- **A flat effect level per definition is unsound as a summary.** beichte
  analyzes `(fn [f] (f 1))` as `:pure` (probe, §2.4), because calling a local
  is `:pure` (`beichte/src/beichte/analyze.clj:407, 409-411`). It stays sound
  at call sites only because merely *referencing* `println` counts as `:io`.
  If a specializer cached "this HOF is pure" and used it to CSE calls, it
  would be wrong. Klara's effect domain needs latent (arrow) effects.

**J-D5. Several systems never conflict on facts, but they can conflict on the
reference semantics.** The meet of sound facts is sound only if every domain
is sound for the *same* semantics. Two live mismatches:
- ansatz maps malli `:int` to `Nat` (`ansatz/src/ansatz/malli.clj:224-227`)
  and emits auto-promoting `+'` (`src/ansatz/codegen.clj:122-128`). A law
  proved over `Nat` does not license a rewrite of Klara's `+` on longs, which
  throws on overflow, unless there is an overflow side condition.
- Elixir's strong arrows rely on the BEAM raising on a bad domain
  (`apply.ex:23-27`). Clojure's `get` returns nil on a non-map, so it is not
  a strong arrow.

The prerequisite is Klara's small-step semantics (05 §7) as the one `γ`
target, with host behaviour modelled explicitly at Tier H.

**J-D6. The Typed Clojure fork's abstract-interpretation plan builds a direct
product, not a reduced one, and its escape transfer is unsound by
inspection.**
- *Direct product.* `join-env` merges the four component maps independently
  (`typedclojure/ABSTRACT_INTERPRETATION_DESIGN.md:191-222`), so no domain
  sharpens another.
- *Widening.* "Types don't need widening" (`:222`) fails once literal or
  count-range types meet loops.
- *Escape analysis.* On `feature/memory-analysis`, `analyze-escape` counts
  only return, closure capture and assignment, and
  `escapes-via-assignment?` is a stub returning `false`
  (`typed/clj.checker/src/typed/cljc/checker/memory_analysis.cljc:196-200,
  203-231`). Passing a binding to an unknown function is therefore not an
  escape.
- *Rewrite keyed on symbols.* `transient_transform.cljc:31-42` rewrites on
  the unresolved symbol `conj`, so a shadowing local is rewritten too.

The 2.37× (`FINDINGS.md:10-14`) is real for the benchmark. The analysis
behind it would not pass J11 (§6).

**J-D7. On the proposed v1 trio, I would replace "usage" with "captures plus
affine authority".** Data usage (in-place update) pays on native RC hosts
(Perceus) and only modestly on the JVM, where transients already exist.
Capture sets pay on day one:
- whether a closure reaches an authority decides fork legality, multi-shot
  resume and the deep value-ness check (G6);
- Klara computes this dynamically already ("Copyability of a closure is
  computed from its captures", G §3.4);
- predicting it statically removes the O(n) traversal and AU1's checks
  (AU7).

Data usage stays a v1.5 domain.

## 2. Per-system survey (verified)

Each entry gives what the system predicts, what that licenses, and what it
costs.

### 2.1 Scala 3: capture checking, direct-style effects, staging, TASTy

**Papers.** Boruch-Gruszecki, Odersky, Lee, Lhoták, Brachthäuser, *Capturing
Types*, TOPLAS 45(4), 2023, doi 10.1145/3618003. Odersky et al., *Scoped
Capabilities for Polymorphic Effects*, arXiv 2207.03402 (EPFL infoscience
290885, cited by `docs/_docs/reference/experimental/capture-checking/internals.md:37`).
Separation checking: Xu, Boruch-Gruszecki, Odersky, OOPSLA 2024 ("Degrees of
Separation"). The venue is from memory and was not checked locally.

**Mechanism.** A capture set is a constant or a variable, under subcapturing
constraints closed under map, filter and intersection: "monadic set
constraints" (`cc/CaptureSet.scala:26-45`).
- The capability classifiers are `Capability` = `SharedCapability` |
  `ExclusiveCapability` (`library/src/scala/caps/package.scala:29, 60, 74`).
  `Control` covers anything that captures a return point: labels, `CanThrow`,
  `Async` (`:87`).
- `SepCheck` enforces "consumed entities cannot be used subsequently" and
  "cannot be consumed in a loop" (`cc/SepCheck.scala:19-30`). That is RFC
  0001's affine settlement, stated as a type rule.
- `CanThrow` is `caps.Control, compiletime.Erased`
  (`library/src/scala/CanThrow.scala:13`): an authority with no runtime
  representation, which is quantity 0 in QTT terms.
- `boundary.Label` is a `Control` capability (`library/src/scala/util/boundary.scala:53`),
  and `boundary.apply` is an `inline` try/catch on label identity (`:71-76`).
- Gears is not in the checkout. The docs name its `Async` as the canonical
  capability (`capture-checking/overview.md:136`), and only tests reference
  it (`tests/neg-custom-args/captures/gears-problem.scala`).

**Predicts and licenses.** Capture sets predict "this closure reaches no
authority, no handler instance, no mutable state". They license:
- fork without traversal and multi-shot resume without a dynamic check
  (RFC 0001 §2, RFC 0002 §5);
- dropping the "revoked handler instance" check on a `perform` whose
  instance provably does not escape (G §3.3);
- erasing settlement-token representation once `SepCheck`-style
  consumption is proved (AU7).

**Cost.** 9864 lines in `cc/` (wc), still `@experimental` in the library.
Klara can carry a much smaller version: it needs no path-dependent types or
boxing, because its capture sets are computed over 12 forms and checked
dynamically when the static layer is off.

**Staging.** `CrossStageSafety` enforces level consistency: a local term may
be used only at its own level, and types are healed through `Type[T]` tags
(`staging/CrossStageSafety.scala:20-35`). It runs after `Inlining`
(`transform/Staging.scala:29`, `Compiler.scala:52-56`). `transparent inline`
must expand during typing, because its result type is refined at the call
site (`docs/_docs/reference/metaprogramming/inline.md:295-299`). Papers:
Stucki, Biboudis, Odersky, GPCE 2018; Stucki, Brachthäuser, Odersky, GPCE
2021. For Klara, a static level domain predicts "no scope extrusion", which
licenses erasing v2 §6's dynamic `close` check. Transparent inline is the
counterexample to the narrowing doctrine: it lets expansion change typing.
Klara's syntax extensions may change meaning, as definitions do (D-D2), but
no *type* may feed back into expansion.

**TASTy.** Versioning contract: same major; and either an equal minor with an
equal experimental version, or an older minor with experimental 0
(`TastyFormat.scala:315-344, 380-392`). The format has extensible sections
(ASTs, Positions, Comments, Attributes, `:394-397`). Attribute tags are
grouped into categories whose payload size can be computed generically, so a
reader can skip unknown tags (`:282-300`). Klara should adopt both: per-domain
evidence sections that a tool without that domain can skip, under a
major/minor/experimental contract.

**For RFC 0001 and RFC 0002.** Take three things:
1. Classifiers as the authority taxonomy: Shared ≈ data and scoped handler
   instances; Exclusive ≈ resources and settlement rights; Control ≈
   continuations and labels.
2. Consume/loop rules as the static form of AU1.
3. Erased capabilities as the target of check erasure.

Do not take the type syntax, the boxing (unnecessary when the core is
untyped), or a checker that discards its results.

### 2.2 Typed Clojure: occurrence typing, annotation corpus, the fork

**Paper.** Bonnaire-Sergeant, Davies, Tobin-Hochstadt, ESOP 2016. Occurrence
typing comes from Tobin-Hochstadt and Felleisen, ICFP 2010 (*Logical types
for untyped languages*).

**Mechanism.** Results carry propositions and *objects*, which are paths from
a local. For example, `first` returns `:object {:id 0 :path [(Nth 0)]}`
(`typed/lib.clojure/src/typed/ann/clojure.cljc:2111-2115`), predicates are
declared with `t/Pred` (`:1646`), and `update-with-proposition` refines along
paths (`typed/clj.checker/src/typed/cljc/checker/update.cljc:476`). The base
corpus is 2755 lines with 479 `cc/` entries (wc and grep). Some entries give
up, for example `get-in → t/Any` (`:2207`).

**Predicts and licenses.** Occurrence typing predicts the shape of a local on
each branch. It licenses removing type checks and casts in `prim` calls,
monomorphic dispatch on a branch, unboxed field access after a shape test,
and dead-branch elimination.

**What porting onto the 12-form core simplifies** (H1–H5 of
studies/typedclojure.md):
- *H1.* The analyzer fork disappears. The checker is a client of the K0 AST.
  The 1.11/1.12 shims (`check.cljc:650`, `utils.cljc:518`) have nothing left
  to shim.
- *H2.* No per-macro rules are needed for correctness. `let` destructuring
  (398 lines of rule) becomes core `let` + `prim` gets. Rules return only as
  optional precision and blame aids carried by the syntax extension.
  Provenance comes from scope-set syntax, not from `:raw-forms`.
- *H3, H4.* `def` is `perform :world/define`, so annotations are
  definitions with CodeIds and the checker mutates no global environment.
  This makes H3's verdict function well-defined.
- *Host forms.* `.`/`new` are `perform :host/*`. Their types come from a
  quarantined Tier H oracle, not from mirroring Compiler.java.
- *Loops.* `loop` is `letrec` with a self tail call. This needs a fixpoint
  with widening, which Typed Clojure avoided by requiring annotations.

**What porting does not simplify.**
- *Predicate identity.* In the core, `(number? x)` is
  `(app (resolve number?) x)`. The occurrence fact is a basis fact on the
  binding of `number?`, a recorded read.
- *Polymorphic HOF inference.* Symbolic closures and their limits
  (`check/fn.clj:227-229`) remain.
- *The corpus.* It must be re-authored. See §7 (e) on licensing.

### 2.3 Elixir: set-theoretic gradual types

**Papers.** Castagna, Duboc, Valim, ‹Programming› 8(2), 2024 (arXiv
2306.06391); Castagna, Lanvin, Petrucciani, Siek, POPL 2019 (gradual typing
as a new perspective).

**Mechanism.** `dynamic()` is a bounded range (`descr.ex:87, 358`), maps are
open or closed (`:102, 109-110`), and stdlib signatures are strong arrows
(`apply.ex:23-27`).

**Predicts.** Elixir predicts definite failure, dead clauses and redundant
patterns, with no runtime casts. That is "gradual without blame cost":
nothing is inserted, so nothing is paid.

**Licenses.** For Klara, a set-theoretic shape domain is the right
*representation* for occurrence typing: unions, intersections, negation, and
open maps for Clojure's map-as-record idiom. Disjointness proofs license
dropping clauses, and closed-map facts license fixed-layout field access
under v2 §9's exact-layout guard.

**Cost.** Precision is traded for size under a hard cap (`apply.ex:16`).

**Rule to carry over.** Infer, never require; report provable errors only;
one finding per definition (elixir-types.md verdict).

**Caveat.** Strong arrows must be declared per `prim`, against Klara's own
semantics, never assumed from the host.

### 2.4 Effect and capability types: Koka, Effekt, beichte

**Koka** (Leijen, MSFP 2014 / POPL 2017; Xie and Leijen, ICFP 2021). Effect
rows predict which operations a call may perform. `isMonEffect`
(`Core.hs:872-878`) licenses non-CPS code for every application without
`ResumeMany` operations or an open row. `isTotal`/`hasTotalEffect`
(`Core.hs:813-860`) licenses floating, inlining and reuse.

**Effekt.** Covered in note G. Its key result is that a statically known
handler plus stack shape eliminates handler abstractions (ICFP 2020, Thm
5.5). Klara reaches it by staging (RFC 0002 §3). A static effect domain adds
one thing staging cannot provide: a *certificate* that the region performs no
operation outside the known handler set, which licenses dropping the fallback
arm entirely (G §3.1, condition 3).

**beichte** (replikativ, Apache-2.0) is the existing effect predictor. It
uses a four-point lattice `:pure < :local < :mutation < :io`, and unknown
code defaults to `:io` (`analyze.clj:346-366`). The probe was run with
`clojure -M -e` in `../beichte`:

| Form | Result |
|---|---|
| `(fn [f] (f 1))` | `:pure` |
| `(fn [] (println 1))` | `:io` |
| `(let [app (fn [f x] (f x))] (app println 1))` | `:io` |
| `(let [m (java.util.HashMap.)] (.put m 1 2) m)` | `:io` |

So it is sound at use sites but has no latent effects: creating a closure
counts as running it, parameters count as pure, and local host mutation counts
as `:io`. Two further problems: its cache is keyed by var, not by content
hash, and it reports one level where Klara needs labels and operation classes.
Klara needs `ε ::= {ℓ:class} ∪ ρ`, with arrows carrying latent ε and row
variables for HOF parameters.

### 2.5 Refinement types

**Papers.** Rondon, Kawaguchi, Jhala, *Liquid Types*, PLDI 2008; Vazou et
al., ICFP 2014. Xi and Pfenning, PLDI 1998, eliminate array bounds checks
with dependent types.

**Mechanism.** Liquid inference *is* abstract interpretation: predicate
abstraction over a finite qualifier set, with a fixpoint over conjunctions.
So it slots into §3 as one more domain.

**Predicts.** Bounds (`0 ≤ t < count ys`), non-overflow and non-nil.

**Licenses.**
- Check elimination in `nth` and array access.
- Unboxed `long`/`double` loops once overflow is excluded. Klara's `+`
  throws, so "cannot overflow" is what licenses dropping the
  `Math.addExact` path.
- `within` metrics on numeric ranges.

**Cost.** SMT per constraint, so it belongs in level 0b. On the JVM, C2
already removes many loop range checks, so the payoff is concentrated in
persistent-vector `nth` and on the native host.

### 2.6 Dependent types via ansatz

**What it is.** A Lean 4 CIC kernel in Java/Clojure, Apache-2.0, with malli
schemas as the on-ramp (`ansatz/README.md`).

**Its role here.** It certifies *laws* (Foldable fusion, monoid
associativity, simulation lemmas for IR passes). It does not certify programs
at scale. v2 §7 already states the licence rule: proved means the guard may
be removed.

**Obligations.**
- The certificate must name the checker version, the bundle cohort and the
  dependency closure (v2 §11).
- The law must be stated over Klara's semantics, not over `Nat` (J-D5).
  `codegen.clj:122-128` shows ansatz's own runtime chose `+'` to stay
  faithful to `Nat`. Klara's `+` is not `+'`.

### 2.7 Quantitative and graded types

**Papers.** Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS
2018; McBride 2016; Orchard, Liepelt, Eades, *Quantitative Program Reasoning
with Graded Modal Types*, ICFP 2019 (Granule); Brady, ECOOP 2021 (Idris 2).

**Grades and what each licenses.**
- 0 → erase: authority tokens after static proof, phantom evidence.
- 1 → consume or reuse in place: settlement, budget, evidence spending, and
  data reuse (Perceus, Reinking et al., PLDI 2021).
- ω → share.

Granule's grades generalize to semirings, which also cover cost and
privacy-style budgets (E5's budget vector).

**Cost.** Linear-time checking for the affine fragment. The difficulty is
inference across HOFs, where Klara's dynamic fallback keeps the layer
optional.

### 2.8 Abstract interpretation as the frame

**Papers.** Cousot and Cousot, POPL 1977 and POPL 1979 (where the reduced
product is introduced); Cousot, *Types as Abstract Interpretations*, POPL
1997; Cousot, Cousot, Mauborgne, FoSSaCS 2011 (reduced product ≈
Nelson–Oppen); Cousot et al., ASIAN 2006 (Astrée's iterated reduction through
communication channels).

**The common reading.** Every system above is a Galois connection
`(℘(Traces_K), ⊆) ⇄ (D_i, ⊑_i)` over Klara's semantics, and soundness is
`α ∘ ⟦·⟧ ⊑ ⟦·⟧♯_i`. Binding-time analysis is another such domain (note C's
grades), as is Scala's level discipline.

## 3. The composition framework

**3.1 Product with declared reductions.** Each domain `D_i` provides `⊥`,
`⊑`, `⊔`, a widening `∇`, transfer functions for the 12 forms, and a
*summary* type for definitions. The analysis domain is the product
`Π D_i`. A reduction `ρ: Π D_i → Π D_i` must satisfy `ρ(a) ⊑ a` and
`γ(ρ(a)) = γ(a)`. It is assembled from pairwise *channels* that domains
declare explicitly, as in Astrée:

| Channel | Example |
|---|---|
| shape → effect | `x : Long` ⇒ `(prim :add x 1)` cannot raise `ClassCastException`; only `:exn/overflow` remains |
| refinement → effect | `x < MAX` ⇒ `:exn/overflow` absent |
| capture → usage | empty capture set ⇒ closure usage ω is legal |
| effect → capture | region performs no `Control` op ⇒ no continuation capture ⇒ no host frame obligation |
| shape → capture | a value of a closed data shape holds no authority, which settles G6 for that value |

Reductions only meet, so they cannot change meaning. If a reduction yields
`⊥` at a reachable node, two domains disagree, or the code is dead. The
framework reports this and uses neither fact, which is the provable-errors
discipline applied between domains.

**3.2 Evidence slots.** The v0 analyzer already gives each node `:evidence {}`
(`lambda-join/v0/src/v0/analyze.clj:8-13, 34`), a path for every node
(`with-paths`, `:173-185`), and identity that excludes evidence
("Evidence never participates in identity", `:216-219`). v0's gaps:
- its op set is Clojure's special forms, not the 12 forms;
- the only evidence ever written is `{:tag t}` (`:190-205`);
- evidence carries no provenance.

The format I propose, per node, keyed `(CodeId, path)`:

```clojure
{:shape   {:fact ...  :grade #{cell...}  :by [:klara.shape "0.3.1"]  :reads #{[sym codeid summary-hash] ...}}
 :effect  {:fact {:ops {:choose :general :log :tail} :rho nil} ...}
 :capture {:fact #{h1 :auth/r} ...}
 :bt      {:fact :S ...}}                 ; note C's grade
```

`:grade` is note C's assumption set (§4). Evidence is stored in TASTy-style
sections, one per domain, skippable by tools that lack the domain, under a
major/minor/experimental version contract (§2.1). R3 extends to evidence:
deleting it changes no observation.

**3.3 Incremental checking.** Every domain gives a per-definition verdict
`V_i(def) = F_i(CodeId, checker_i version, {(name, CodeId, summary_j hash) ∈ reads_i})`,
where the read-set is recorded by the shared tracking engine (v2 §6; Typed
Clojure's `with-recorded-deps` is the precedent, studies/typedclojure.md
§3(d)). Two rules make it cheap:
1. **Per-domain early cutoff.** A dependent reads summaries, not bodies.
   Adding a `println` to `inc` changes its effect summary but not its shape
   summary, so only effect dependents re-run (Mokhov, Mitchell, Peyton
   Jones, *Build Systems à la Carte*, ICFP 2018).
2. **Reduction channels are recorded reads.** If shape(`g`) used
   effect(`f`) through a channel, `(f, effect-summary-hash)` is in
   shape(`g`)'s read-set. Without this, early cutoff is unsound.

A mutually recursive group of definitions is checked as a unit, to a
fixpoint with widening. Checking is never on a redefinition's critical path
(R2). A definition with a stale verdict runs at T1 with no evidence.

## 4. Specializer interface

The specializer asks one question: `(entails? node fact) → {:proved g |
:refuted | :unknown}`, where `g` is the grade of the proof. The grade decides
the realization:

| Grade of the supporting evidence | Realization | Check location |
|---|---|---|
| `S`: a closed fact, local AST only | **certificate**: no guard | none |
| `A` with world cells only, i.e. summaries of other definitions | **certificate under basis**: no runtime guard; the executable registers on one protector per (definition, summary), so R1's publication cost stays independent of dependent fanout | writer, at publication |
| `A` with argument-guard pseudo-cells (profile, `:stable`) | **guarded assumption**: entry guard, fallback to T1 or replay from region entry (G §3.1, condition 2) | reader, at region entry |
| `A` with Tier H oracle cells (reflection, annotation corpus, linked code) | guarded, or trusted with the trust recorded in the receipt | reader, or none plus receipt |
| a checked claim (v2 §7.2) | the check *is* the guard, with blame; downstream it is a certificate dominated by the check (H5) | reader, once |
| `:refuted` | do not specialize; report as dead code or a wrong profile | — |

Two consequences. First, a level-0 fact can *discharge* a level-3 guard: a
profile says `xs : (vector long)`, and occurrence typing proves it on the hot
path, so the guard is dropped there and kept elsewhere. Second, a level-2
surrogate may choose which `entails?` queries to run (VOC, 05 §9.2), but its
answer is never an input to the table above (05 §9.5).

## 5. The v1 subset

Proposal: three 0a domains, with 0b deferred.

1. **Shapes with occurrence typing**: set-theoretic, open maps, inferred,
   Elixir rules.
2. **Effects with operation classes and latent rows**: labels, the
   tail/abort/general classification, and the reversible/irreversible bit.
3. **Captures with affine authority**: which handler instances and
   authorities a value reaches, plus consume-once for Exclusive authorities.

The binding-time grade (note C) is the specializer's own fourth domain and
already exists in the design.

Justification from `02-examples.md`. E5 shows a requirement that no domain
covers; it is an open gap:

| Example | Shapes | Effects | Captures/authority |
|---|---|---|---|
| E1 SMC | `x` is a double ⇒ unboxed loop; `ys` is a vector ⇒ direct `nth` | `observe` is tail ⇒ direct call; `choose` is general only under `smc` ⇒ a narrow CPS region | the continuation captures no resource ⇒ resampling forks without a check; address linearity (each `[:y t]` observed once) is usage 1 on evidence |
| E2 city | `within` needs a `Distance` for the result shape: a static error instead of the dynamic one in G3 | `spending` is pure ⇒ licensed for GPU `translate` (beichte's purpose) | `:coupled` shares the randomness key; otherwise the key is split, an affine token |
| E3 REPL | — | — | the framework itself: the content-hash verdicts of §3.3 under re-expansion |
| E4 interop | cheshire output is a Tier H shape oracle, guarded | lazy-seq producer is pure ⇒ the seq is a value (G7) | a closed data shape with empty captures ⇒ deep value-ness without a walk (G6) |
| E5 training | — | `:iterate` is general | budget is an affine split (G8); validation and claim evidence are distinct tokens, and the domain proves they are never joined (G9): **Open**, since usage grades alone do not express "not joined" |
| E6 agent | — | the branch body performs no irreversible op ⇒ no intent queue; otherwise intents are deferred (G10) | the connection is a branchable authority, settled once (AU2) |

**Deferred.**
- Refinements (0b; E1's bounds are a JVM micro-win).
- Data usage for in-place update (v1.5 with the native host).
- Graded cost (feeds level 1, not certificates).
- Dependent types beyond law certificates (already in v2 §7).

## 6. Obligations and falsifiers

| Id | Obligation | Status | Falsifier / check |
|---|---|---|---|
| J1 | Deleting all evidence preserves results and effect traces (R3 extended) | Conj | differential runs with evidence on and off over the E1–E6 programs |
| J2 | Each 0a domain is sound for the K0 reference interpreter | Open | generate random 12-form terms; any certified fact violated by a run |
| J3 | Every reduction is reductive and γ-preserving | Open | property test `γ(ρ a) = γ a` on finite models; any reachable `⊥` is reported, never used |
| J4 | Per-domain early cutoff: a body edit that keeps the summary re-runs 0 dependents in that domain | Conj | count re-checks over an edit script; a channel read missing from a read-set is a soundness bug |
| J5 | 0a checking costs ≤ 5 ms p99 per definition on a 10k-definition corpus and stays off the publication path (R1/R2) | Open | timing; Elixir's history (§2.3) is the warning |
| J6 | No effect summary claims purity for a definition that calls a parameter | **Refuted for beichte** (`(fn [f] (f 1))` → `:pure`) | the Klara domain must report a latent row `ρ` |
| J7 | Regions certified free of general operations, compiled without CPS, give identical traces (EF3) | Conj | partial-cps differential (F12 extended past its grammar) |
| J8 | With the capture layer on, AU1's adversarial suite passes and fork copies skip traversal (AU7) | Open | Codex experiment 1 with the layer on and off |
| J9 | A law certified over `Nat` licenses a `long` rewrite only with an overflow side condition | Conj | a fused rewrite that changes an `ArithmeticException` trace |
| J10 | Occurrence typing over K0 handles destructuring expansions with no macro rule | Conj | Typed Clojure's `let` test cases, re-expressed (not copied), checked on expanded core |
| J11 | Transient rewriting fires only when no alias escapes through argument passing | **Refuted by inspection** for the Typed Clojure fork | `(let [v []] (stash! v) (conj v 1))` with an opaque `stash!` |
| J12 | Inferred capture sets reach the store; Scala's discard pattern is not repeated | Design | evidence sections present for 100 % of checked definitions |

## 7. Questions for Christian

1. **Level 0a and 0b.** Do you accept splitting level 0 by cost, with 0b
   (SMT, ansatz) scheduled by value of computation like levels 1–3?
2. **Basis facts as certificates.** Is "no runtime guard, writer-side
   invalidation, one protector per (definition, summary)" an acceptable
   reading of "certified", given R1?
3. **v1 trio.** Captures plus affine authority instead of data usage (J-D7)?
   Data usage would then arrive with the native host.
4. **One capture domain for handler instances and authorities.** This is RFC
   0001 Q3. With Scala's classifiers I think the answer is yes: Shared,
   Exclusive and Control map to scoped instances, affine authorities and
   continuations.
5. **ansatz semantics.** Should Klara laws be stated over a faithful `long`
   with overflow (the wandler embedding), or over `Nat`/`Int` with side
   conditions discharged by the refinement domain?
6. **Licensing (e).**
   - *Typed Clojure* is EPL-1.0 (`typedclojure/LICENSE:1`). Klara is
     Apache-2.0 (`klara/LICENSE`). Port ideas only. I suggest the clean-room
     rule already used for Clojure (00-design-space.md:40-44): agents writing
     Klara's `prim` signatures do not see `typed/ann/clojure.cljc`, and the
     signatures are derived from Klara's spec and checked against behaviour.
   - *Your own fork code.* `memory_analysis.cljc` and `transient_transform.cljc`
     carry the upstream EPL header naming Bonnaire-Sergeant and Hickey. Are
     they solely yours, so that you could relicense them? I would treat them
     as EPL until you say otherwise.
   - *Apache-2.0 sources.* Scala 3, Koka, Elixir, ansatz and beichte are
     Apache-2.0 (each repo's `LICENSE`), so porting code needs only NOTICE
     attribution.
   - *Not checked locally.* Liquid Haskell's and Granule's licences.
7. **Annotation surface.** One type language whose clauses address several
   domains (`^{:- T :! ε :^ C}`), or one annotation key per domain?
