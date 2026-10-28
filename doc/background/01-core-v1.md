# Klara Core v1 — first design iteration (2026-10-27)

Synthesis of the five research notes in `research/` (A core calculus, B memory
model, C staging, D dispatch and interop, E resources and learning), read
against each other and against `00-design-space.md`. Status markers as in
`doc/signature.md`: **Holds**, **Conj**, **Open**. Every section names the note
it comes from; details, citations and falsifiers live there.

## 0. What changed relative to the prior design

1. **λ is the definition, the monoidal computer is the interface** (A). D1 said
   "MC substrate, λ surface". A λ-calculus with `quote`, `run` and a
   specializer already presents a monoidal computer (its term model), so the
   spec is a call-by-value λ-calculus and the MC equations (eval-quote, s-m-n)
   are theorems about it. The MC remains the vocabulary of the semantics.
2. **One MC cannot hold non-copyable objects** (A). In Pavlović's definition
   every type has copy/delete and is a retract of P, so a retract of P is
   copyable. The `signature.md` §1 table (W and R without copy) is therefore
   two structures: an MC of data acting on a linear world of resources. This
   link is new work (A-O4).
3. **Three fork structures, not one** (B). "Only values fork" is false in our
   own code: spindel forks atoms and yggdrasil systems. Forking applies a
   per-sort structure: copy for values, mass-preserving split for evidence,
   `branch!` for branchable resources, rejection for plain resources.
4. **`freeze` leaves the semantics** (B). It is a realization step, a no-op
   under reference counting and O(1) on the JVM.
5. **Expansion and specialization share one mechanism but have two
   visibility rules** (C). Expansion defines meaning; specialization must
   preserve it. v0 currently has a measured bug here: redefining a macro
   leaves its users stale and reports nothing (C §1, E0).
6. **Types in dispatch patterns and type annotations must be distinct** (D).
   Raster's `deftm` uses one syntax for both, which makes "annotations never
   change meaning" false from day one.
7. **No single quantale carries cost, error and information value** (E).
   Grades are a product of small algebras; information value is a policy
   input, not a grade.

## 1. The core calculus (A, C)

Call-by-value small-step semantics, de Bruijn locals, deep handlers.

```
e ::= x | (quote d) | (fn [x…] e) | (e e…) | (let [x e] e) | (if e e e)
    | (letrec [(f (fn …))…] e)
    | (resolve id)               read the pinned world
    | (prim op e…)               portable algebra operation (Tier L)
    | (perform op e…)            effect operation
    | (handle e h)               deep handler
    | (specialize e e)           s-m-n; reference meaning = closure formation
```

Twelve forms. Everything else elaborates or becomes an effect operation:
`def` (`:world/define`), `throw`/`try` (`:exn`), host interop (`:host/…`, the
outermost handler is the host), `expand` (`:expand`, returns a program value
plus its recorded reads), `eval` = run ∘ expand under an explicit basis.
Syntax objects with scope sets are values (C §4.2: `quote-syntax`, `lift`).

**Reference handlers** fix the meaning of each effect: `H_world`
(define/resolve/basis), `H_host` (an oracle parameter; theorems quantify over
hosts satisfying a contract), `H_meas` (choose/observe/factor into finite
discrete subdistributions in v1), `H_fork` (split/join with λ∨'s π premise),
`H_expand`. λ∨'s laws are equations these handlers satisfy; inference engines
and optimizing runtimes are other handlers proven or tested against them.

**Continuations** are one-shot by default; multi-shot resumption is allowed
only when the captured context holds no resources or evidence (A-O6, B §4.7).

**Adequacy** (A §4): A1 denotation = observed subdistribution under the
reference handlers; A2 eval-quote and s-m-n hold with program identity modulo
α; A3 resources interpret in the linear world and `run` is natural but not
copyable there (new, **Open**).

## 2. Sorts, forks and the memory model (B, A, E)

| Sort | Structure | Examples |
|---|---|---|
| Value | copy, discard free | scalars, keywords, strings, persistent collections, programs, closures whose captures are all values |
| Resource | discard only (scheduled drop) | channels, files, arrays, Java objects by default, linked-mode Clojure atoms |
| Evidence | split only (mass-preserving) | weights, observations (fit *or* hold out, never both: city R9) |
| Branchable | discard + `branch!` effect with settlement | the world, datahike connections, yggdrasil systems, hosted atoms |

- **Fork** applies each sort's structure; a fork over a live resource is
  rejected. Copyability of a closure is computed from its captures.
- **Uniqueness is evidence, not meaning**: proved-unique ⊐ runtime-checkable ⊐
  unknown selects a representation. Owned runtime: reference count = 1
  (Perceus). JVM: region tokens per node, as transients do, with the measured
  cost that every child copies after a fork (B §0.4, O3).
- **Storage tiers, one rule**: mutability only in the innermost tier where
  uniqueness is known; moving outward (heap → disk → remote) is a freeze at
  that tier's granularity; fork is O(1) on every tier.
- **Representation freedom** requires: value identity unobservable
  (`identical?` is a hint), structural `=`/hash independent of layout,
  unspecified iteration order of unordered collections (the corpus
  randomizes it), ε grades for floating-point relayout.
- **Randomness**: keys are split at a fork by default (independent branches);
  copying a key is legal only through an explicitly *coupled* fork (common
  random numbers, city R1–R2). This is the ESOP paper's identification
  declaration (shared vs fresh names) appearing as a language primitive.

Indicative JVM numbers (B §6, scripts in `research/bench/`): region
transients up to 4.3× faster than persistent updates on an SMC skeleton, flat
unboxed leaves another 1.7–3.2×, still 2.6–3.4× behind clone-on-duplicate
mutable arrays at high write rates.

## 3. Identity and equality (A, B, C)

- Values have no observable identity.
- Programs have **content identity**: the hash of the α-canonical expanded
  source, frozen before optimization. Inspecting a closure's body (`reify`)
  is a reflective effect, not a core operation — the defence against Wand's
  result that observable code identity forbids every optimization.
  Consequence: `(= (fn [x] (+ x 1)) (fn [x] (+ 1 x)))` is deterministically
  false.
- Scope ids derive from (parent context hash, binder path), so the same form
  under the same basis expands to the same canonical output in every fork.

## 4. Staging continuum (C)

- **Grades**: S ⊑ A ⊑ A′ ⊑ D, where A ranges over finite sets of revocable
  assumptions (world cells, argument guards). "Stable" is "dynamic plus a
  named set of facts", not a separate stage. Grades never change meaning.
- **Macros live in the world**; transformers read the world only through the
  recording reader, so expansion leaves a dependency trace.
- **One demanded-computation graph** (`:expand`, `:analyze`, `:specialize`
  nodes, each with recorded reads and receipts), lazy re-verification with
  early cutoff on the expansion output hash.
- **Two visibility rules**: re-expansion is a new definition, visible to a
  running fiber only after it raises its basis; re-specialization swaps in
  immediately, since it is unobservable.
- **Cache across forks**: entries are valid in another fork iff every recorded
  read hashes the same in that fork's basis.
- **Path**: M0 hygienic `eval` with a basis argument, macros in the world,
  trivial `specialize` → M1 residuals with real dependencies → M2 guards,
  inline caches, deoptimization budget → M3 raster as optimizing tier → M4
  collapse to an AOT artifact.

## 5. Dispatch and typing (D)

- **One construct, `defop`, with a declared fragment**: `:single` (default,
  protocol-shaped), `:value` (declared pure key function), `:multiple`
  (opt-in, numerics and kernels, realized by raster).
- **Shapes enter dispatch only by name** (a tag); key-set shapes are checker
  and guard evidence.
- **Extensions have owners**: re-extending your own op at the REPL makes a
  new version; two owners at the same pattern conflict.
- **Dispatch patterns are definitions** (may change results). **Annotations
  are claims** with three grades: *hint* (default: guard plus deopt, never an
  error), *checked* (shallow boundary check, cached per persistent value,
  blame on the annotated definition), *proved* (certificate removes the
  guard). Higher-order wrapping only on request.
- **Static checker**: infer, never require; report only provable errors.

## 6. Clojure interop and hosting (D)

- **Phase 0** uses Clojure's collections, so parity is automatic.
- **Klara types are real JVM classes** implementing, in order: `IHashEq`,
  `IMeta`/`IObj`, `IFn`; for maps `IPersistentMap` + **`MapEquivalence` +
  `java.util.Map`** (both required for symmetric `=`), `IKVReduce`,
  `IReduceInit`; then vectors, seqs (chunked), records. Hash parity through
  Clojure's public hash functions; nothing copied.
- **Klara → Clojure**: IFn calls by `invokeinterface`; non-dynamic Clojure
  vars cached and invalidated through var watches.
- **Loading modes**: *linked* (plain `require`, Clojure state shared by all
  forks, outside the basis guarantees, Tier H) and *hosted* (through Klara's
  expander, forkable). **`clojure.core` is always linked**: it is
  direct-linked, and hosting it would compile EPL source into Klara
  artifacts.
- **Platforms**: a host is a handler stack plus an operations table (Roc's
  platform idea); JVM apps embed Klara as a library, databases exchange
  persistent snapshots only.

## 7. Resources, placement and the learning runtime (E)

- **Static grades** (opt-in narrowing): usage {0,1,ω}, binding time (§4),
  locale requirement, sensitivity (Lipschitz factor).
- **Dynamic receipts** only under `with-ledger`: value, ε vector (per error
  model), cost vector (sequential `+`, parallel `max` on time), evidence ids,
  licence. Without the handler nothing is allocated (target ≤ 2% overhead).
- **Placement surface**: `locale` values, `(translate T e)` as the only way
  across substrates (declared error model, measured cost), `(with-mapper m e)`
  whose contract is Legion's (mappers change speed, never results beyond ε),
  `(within ε e)` as the caller's tolerance.
- **Learning loop**: proposal (fork) → evidence (ground; measurements are
  evidence, split never copied) → certificate (proof / guard+deopt / budgeted
  bound) → adopt (join), with receipts that separate the evidence used to
  *select* a decision from the evidence used to *claim* its gain (ESOP: selection
  is a fork). Replay re-checks certificates, never re-runs proposers.
- **Bounded rationality, smallest formal statement**: policy invariance (any
  allocation policy changes cost and ε, nothing else), budget conservation
  across fork/resample/discard, and known optimal allocations (multilevel
  Monte Carlo, grounding persistence, myopic value of computation) as probes.

**Proposed resolution of the A/E tension.** E asks whether a program denotes a
value or a "ball" of values within ε. I propose: the core denotation stays
exact (A1 unchanged); `within ε` declares a *refinement relation* — the set
of implementations the caller accepts — and approximating handlers are
proved or measured ε-adequate against the exact handler. Fidelity choices are
then legal implementations, and the narrowing doctrine reads "erasing an
annotation preserves meaning up to the declared ε".

## 8. Specification (A)

- **Source**: Lean-4-compatible definitions in ansatz: syntax inductive,
  `step` as a total function, `Step` as its graph. A probe confirmed indexed
  relations with recursive premises, case-analysis proofs and compilation of
  the step function to Clojure; substitution lemmas and the Lean export are
  untested.
- **Reference interpreter**: the compiled `step`.
- **Redex** stays for random testing of λ∨ laws, differential against the
  reference interpreter. **Corpus** is the conformance suite.
- **katzen/GATs** state the categorical *structure* (monoidal, copy/delete,
  MC equations) readably; they cannot state the operational semantics
  (equational theories cannot express ∃-quantified universality or a step
  relation).

## 9. Decisions for Christian (recommendation first)

| # | Question | Recommendation | Note |
|---|---|---|---|
| Q1 | MC of data acting on a linear world of resources and evidence? | yes | A Q1 |
| Q2 | Program identity = hash of canonical expanded source; `reify` an effect? | yes | A Q2 |
| Q3 | Multi-shot continuations only without captured resources? | yes | A Q3 |
| Q4 | `branch` means snapshot; parent-following is a separately named operation? | yes | B Q2 |
| Q5 | Unspecified iteration order for unordered collections; `identical?` a hint? | yes | B Q3 |
| Q6 | Random keys split by default, copied only in an explicitly coupled fork? | yes | B Q1, E R1–R2 |
| Q7 | "Stable" = dynamic plus named revocable assumptions? | yes | C Q1 |
| Q8 | Macro effects (files, datahike, LLM calls) only through the expansion handler, recorded as inputs? | yes, with an unrecorded escape hatch marked in provenance | C Q2 |
| Q9 | Running code sees re-expansion only at basis raises; reactive raising opt-in? | yes | C Q3 |
| Q10 | Distinct syntax for dispatch-pattern types vs annotations (raster adapter)? | yes | D Q1 |
| Q11 | Wrong annotation: silent slow path by default, contracts opt-in per module? | yes | D Q2 |
| Q12 | Linked Clojure code (incl. `clojure.core`) outside the fork guarantees? | yes, documented | D Q3 |
| Q13 | Information value a policy input, never a grade? | yes | E Q1 |
| Q14 | Exact denotation + `within ε` as refinement relation (§7)? | yes | E Q2 |
| Q15 | Memory and deadlines hard constraints; money and energy traded? | yes | E Q3 |

## 10. Implementation plan: five experiments, smallest first

| # | Experiment | Size | Decides |
|---|---|---|---|
| X1 | Macros in the world with recorded expansion reads, on v0 (C §6) | ~200 LOC, 1–2 days | fixes the measured v0 bug; tests early cutoff, fork isolation, basis isolation |
| X2 | `KMap` through `clojure.core`: property tests for `=`/hash symmetry, benchmark vs Clojure maps, one `defop :single` vs a protocol (D §6) | 2–3 days | interop parity and dispatch cost (≤1.1× delegate, ≤1.2× protocol) |
| X3 | Klara Core v1 in ansatz: 12-form syntax, `step`, progress/preservation for scoping, compiled interpreter differential against `v0.kernel` on its corpus (A §6) | ~1 week | whether ansatz can carry the spec (kill rule: >2× the effort of `Core.lean`) |
| X4 | Allocation over translate levels on the city with receipts: best single level vs uniform vs Giles MLMC at equal budget (E §6) | ~300 LOC | whether dynamic receipts earn their keep (kill rule in E §6); doubles as material for the demo |
| X5 | The SMC memory benchmark in Koka and Lean 4 vs JVM tokens (B §6, E2) | ~2 days | whether the owned runtime must be the performance reference for fork-heavy inference |

X1 and X2 are independent and small; X3 is the formal backbone; X4 connects
to the city demo; X5 informs the owned-runtime decision, which is not needed
before 2027.

## 11. Decision log (Christian, 2026-10-27)

- **Q8 (macro effects)**: macros are pure by default; effects are allowed
  through a lightweight explicit opt-in, which the expansion handler records
  as inputs (content hashes), so invalidation keeps working.
- **Q11 (annotations), revised**: follow the Clojure/JVM split rather than
  D's silent-fallback default. *No annotation* → generic dynamic code (slow is
  fine). *Annotation present* → a checked claim: a cheap guard that throws
  with blame on mismatch, which lets the compiler emit unboxed code without a
  boxed fallback. (Clojure behaves this way already: a missing hint means
  reflection, a wrong hint is a ClassCastException.) A separate `:hint` grade
  remains for purely speculative JIT advice. This is exactly the SNAPL'15
  gradual guarantee: removing annotations never breaks a working program;
  adding them may only add errors. Per-context defaults stay open.
- **Q12**: linked Clojure code, including `clojure.core`, is outside the fork
  and basis guarantees, documented.
- **Q6**: explained; decision pending.
- **Meaning under learning**: meaning stays invariant and is fixed by the
  system, but may be defined as the *limit* of a convergent process (fixpoint
  iterations, training, controllers) with convergence rates and predictors
  attached. See §12.
- **Typed core**: no; untyped core (see §12).
- **Later milestone (not now)**: a comparative value proposition — what
  Klara adds over staying on Clojure, over moving to Lean 4, and against a
  set of other languages (Julia, Koka, Racket, Mojo, Unison, …); also a
  deliberate contrast with the JVM's design (dynamic speculative runtime
  under a static surface language).

## 12. Convergent meaning and the place of types (proposal)

**Convergence.** Denotational semantics already defines the meaning of
recursion as the limit of finite approximations (Scott). Generalize that
quantitatively: `(converge step x0 opts)` (an `:iterate` effect) denotes the
limit of the iteration where it exists, or — when the limit is not unique, as
in neural-network training — any point satisfying a declared specification
within ε (the refinement relation of §7). Executions are approximants
carrying receipts with ε_n at iteration n and a licence: *proved* (a
contraction or convergence theorem in ansatz/Lean, e.g. Banach's fixpoint
theorem from Mathlib gives a rate), *guarded* (a checked a-posteriori
residual bound), or *predicted/measured* (a learned convergence predictor,
marked as an estimate). The allocation policy decides when to stop
(continue while the expected improvement is worth its cost), and speculative
forks run alternative approximation strategies whose results are joined by
value. The language needs exactly one construct for this; the rest is
handlers and receipts.

**Types.** The core stays untyped (dynamic), like Scheme and Clojure: the
operational semantics, the spec and the corpus are about untyped programs.
Two things are typed nonetheless:
1. **Sorts are tracked dynamically** in the core (value / resource /
   evidence / branchable, as a tag checked at fork and at copy), and
   statically only in the affine narrowing layer.
2. **The compiler's internal IR is typed** (shapes, representations,
   uniqueness), produced by inference and annotations, as raster's IR
   already is. This inverts the JVM: the JVM has a typed bytecode under a
   speculating runtime; Klara has an untyped surface and core over a typed,
   evidence-carrying IR that the runtime speculates on.

## 13. "Macros" dissolve into two constructs (proposal, 2026-10-27)

- **Q6 decided**: splittable random keys (counter-based, e.g. Philox/Threefry
  or SplitMix), split at forks by default, shared only in a coupled fork.
  Counter-based keys also give the city's counter-addressed draws (E R1).

In the staging picture a macro is a program at an earlier stage that maps
code to code: `quote`/unquote are staging brackets, `run`/`eval` is the
universal evaluator. Its known compositionality problems are (1) names
(hygiene), (2) no interface — what syntax it accepts and what it produces is
undeclared, (3) interference between macros (one needs another's expansion:
`local-expand`), (4) effects and expansion order. Klara therefore replaces
"macro" by two constructs with different guarantees:

1. **Staged functions (code generators).** Ordinary functions over code
   values: brackets build code, escapes splice, `run`/`specialize` execute.
   Compositional because they are functions. Typed staging in the BER
   MetaOCaml style (`code<τ>`: generated code is well-typed by construction;
   ../ber-metaocaml, Kiselyov FLOPS'14) is an opt-in narrowing layer. This
   is the same terrain as partial evaluation, so staging and code generation
   are one mechanism.
2. **Syntax extensions (notation).** Surface transformers into core with a
   declared interface: an input grammar (Racket syntax-parse style syntax
   classes, giving good errors) and an output language they must elaborate
   into. Lean 4's split between macros (syntax → syntax) and elaborators
   (syntax → typed term, with access to type information) is the closest
   precedent. (Correction, research/H: metacarp types a macro *as a program over
   forms* — checking that the transformer itself cannot go wrong — not the
   generated object program; its macros stay unhygienic. A different rung of
   the ladder: "transformer well-typed", below "output well-formed".)

Guarantee ladder, à la carte: hygiene (always) → declared input grammar (new
extensions) → output checked well-formed in core at expansion (cheap,
always) → typed code (opt-in). Clojure `defmacro` is a compatibility form of
(2) without a grammar and unhygienic, marked in provenance.
