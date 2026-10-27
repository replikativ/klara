# C. The staging and partial-evaluation continuum (research note, iteration 0)

2026-10-27. Aspect C of `../00-design-space.md`. Builds on D2/D14/D15,
language.md §1.3–1.5 and §8.1–8.6, spine.md C-TOW-1..7, and v0 rings 1–3.

## 0. Disagreements first

1. **C-TOW-1 merges a definitional step with an optimizing step.** In
   spine.md:153 macroexpansion, constant folding and JIT specialization
   are "one operation". They share the binding-time skeleton, but their
   obligations differ. Expansion *gives* the program its meaning, and no
   `≡ run` law constrains it. Specialization must leave meaning unchanged.
   So the two need different invalidation protocols. Re-expansion produces
   a **new definition in a new world**, visible only when a fiber raises
   its basis. Re-specialization is a **transparent swap** that may happen
   at any time, because nobody can observe it. If the two share one
   protocol, either specializations stay stale until the next raise (too
   slow) or macro edits leak into running fibers (unsound). My proposal
   keeps one mechanism, the demanded-computation graph over the world,
   and gives it two visibility rules.

2. **"Stable" is a family of points, not one point.** In the lattice
   `static ⊑ stable ⊑ dynamic` (D2, C-TOW-2), *stable* means "known now,
   revocable". Meaning-wise a stable value is dynamic; "stable" describes
   whether a residual is still valid, not what the term means. For precise
   invalidation the grade has to say *which* facts were assumed. I propose
   grades `S ⊑ A ⊑ A′ ⊑ D` for finite assumption sets `A ⊆ A′`, where join
   is union of assumptions. The three-point lattice remains as surface
   syntax.

3. **C-TOW-3's three conditions (hygiene, content-addressing, certified
   swap) are not enough, and v0 shows it.** v0 hashes definitions by
   content, yet its deep hash leaves out the macros consulted during
   expansion. I ran this. Redefining a macro leaves every user green and
   stale, with zero stale entries reported (§1, experiment E0). There are
   two ways to read this. Either content-addressing must be *defined over
   the expansion read-set*, which is a stronger claim than hashing the
   source, or **read-set completeness** is a fourth condition. A fifth
   candidate is **basis isolation**: running code must not observe
   re-expansion before it raises its basis. v0's host-eval path breaks
   this (defs.clj:211-214).

4. **"Beyond Racket at the top level" is achievable, but not by fixing
   Racket's expander.** Racket's top level is "hopeless" because it
   *commits* to a resolution against a namespace that keeps changing
   (studies/racket-rhombus.md:27, `bind-top.rkt:10-22`, `fallback.rkt`).
   In Klara, an expansion is a function of an explicit basis, and the
   identifier resolutions it performs are recorded reads. Then the top
   level is incremental rather than hopeless: changing what a name
   resolves to marks the expansion dirty. The price is that re-expansion
   never mutates running code.

5. **Shipping only `eval` is fine, provided its signature takes a basis
   from day one**: `(eval stx)` ≡ `(eval stx (current-basis))`. Julia
   bolted world age on in 2017, six years late (design-decisions.md:758-761).
   An `eval` that reads ambient state can be neither cached nor forked.

## 1. What our prior docs and code already settled

**Decisions (doc).**
- Hygiene via scope sets plus expansion as a handler-selected effect.
  Phases generalize to the staticness lattice (design-decisions.md:25-69,
  constraints at :56-62). Racket's phase tower is a separable third, and
  handlers replace it. Racket spent its patches on cross-context
  re-expansion, on expander state under reentrancy, and on `quote-syntax`
  pruning (studies/racket-rhombus.md:49).
- `quote`/`run`/`specialize` are specified core forms. Programs are hash-identified
  values (design-decisions.md:10-23; language.md:36-39).
- The collapse doctrine: dynamic in semantics, AOT as an explicit,
  named collapse mode, never a side effect (language.md:40-47;
  design-decisions.md:819-833; language.md:224-229).
- The JIT is a learning loop with a ledger. Learned passes sit in the
  proposal position, and certificates gate what runs (language.md:48-57).
- Incrementality (language.md:172-192): content hashes as identity, a red-green layer
  over ~5 aspects per def with the interface hash as firewall, dynamic
  read-tracking, fibers pinning a basis, lazy invalidation, rustc's 1/32
  rotating re-verification, and **all definitional state (vars, types,
  macros, imports) under one visibility mechanism from day one**.
- Speculation (language.md:194-213; design-decisions.md:762-779):
  Truffle's Assumption and CyclicAssumption (publish first, then
  invalidate; install-time bailout), V8's poisoning and soft deopts, a
  bounded reoptimization budget (15 deopt cycles, 100 compiles per target).
- The staging/macro division (language.md:266-281, after Zig): staging
  owns value-keyed generation, and macros own binders and control. The
  specialization cache uses interned-argument keys, effect poisoning and
  fuel replay.
- spine.md:153-159 holds C-TOW-1..7. C-TOW-5 says partial CPS is a
  two-colour BTA. C-TOW-6 says amortized inference is the first Futamura
  projection of an inference algorithm.

**Code (v0, verified by running it).**
- `expand.clj` keeps scopes in symbol **metadata** (:39-44). Resolution
  takes the largest subset, and ambiguity raises an error (:136-151).
  Macro calls use the flip discipline (:296-305). `defmacro*` evaluates
  the transformer at expansion time (:338-345). Macros, however, live in a
  **per-ctx atom** (:115-121, :128-130), not in the world. Scope ids and
  renames come from per-ctx counters and gensym (:27-31, :174).
- `defs.clj` computes three hashes: shallow (α-invariant), deep, and
  interface (arity surface). Dependencies are the var-refs of the
  *post-expansion* AST (:170-177, :203). Red-green invalidation with
  early cutoff is at :247-271. Recheck re-runs `defv!`, which includes a
  host `eval` (:237-245, :213).
- `stage.clj` memoizes by static-argument values, poisons on effects, and
  replays fuel (:74-110). `depend!` is a stub (:62-68), and invalidation
  is coarse (:128-133).
- `world.clj`: `with-basis` and `raise-basis!` play the role of Julia's
  `latestworld` (:92-110). Forks are free (:59-62). History is linear,
  and there are no dependent-code lists (:30-32).

**Experiment E0** (script in the session scratchpad, run against unmodified v0):
```
(defmacro* twice [e] (qq (+ ~e ~e)))   (def f (fn [y] (twice y)))   (f 3) ;=> 6
(defmacro* twice [e] (qq (* ~e ~e)))   (invalidate wo ctx 'twice)
;=> {:stale [] :green [] :cutoff []}   (f 3) ;=> 6   (:deps f) ;=> #{}
(= (add-scope 'y 1) (add-scope 'y 2)) ;=> true, equal hashes too
expanding (let* [z 1] z) twice in fresh ctxs ;=> z815 vs z816, yet α-canonical content-hash is equal
```
This gives three facts. Macro dependencies are invisible. Syntax objects
that differ only in scopes are `=`, so any cache keyed on the form
silently merges different bindings. Expansion output is not stable in
content, but the α-canonical hash is. The same form-keyed hazard exists
in `partial-cps/…/ioc.clj:70-76`: its `expansion-cache` is keyed by
`form` alone, while `expand-macro` also takes `env`.

**Siblings.** `wandler/jit/swap.clj:40-80` already has the right deopt
shape: a guard pre-check, a lossless fallback to the original on the
*same* input, and a pin after `cutoff` violations. Spindel's spin cache
(`spin/core.cljc:266-268`) is a single-slot "deps unchanged" cache with
dirty propagation and forkable contexts. That is Adapton's model over
fork-able state.

## 2. External survey (verified)

- **Davies, λ○** ("A temporal-logic approach to binding-time analysis",
  LICS 1996, pp. 184–195; https://www.brics.dk/RS/95/51/). Curry–Howard
  for LTL's "next" operator gives a typed λ-calculus equivalent to
  multi-level BTA. ○A is *open* code: it may mention variables from
  earlier levels, and it has no `eval`.
- **Davies–Pfenning, □** ("A modal analysis of staged computation",
  POPL'96 pp. 258–270; JACM 48(3) 2001; TR
  https://www.cs.cmu.edu/~fp/papers/CMU-CS-99-153.pdf). □A is *closed*
  code, and `eval : □A → A` is sound. *Lesson*: open code composes well,
  and closed code can be run. Racket syntax objects are ○-like and become
  runnable because a namespace closes them. **In Klara the basis is the
  closing environment**: `eval : Syntax × Basis → Value` turns ○ into □,
  and scope extrusion becomes a dynamic "unbound in basis" error.
- **MetaML / MetaOCaml.** Taha–Sheard, PEPM'97 (TCS version
  https://doi.org/10.1016/S0304-3975(00)00053-0). Kiselyov, "The design
  and implementation of BER MetaOCaml", FLOPS 2014,
  https://doi.org/10.1007/978-3-319-07151-0_6, plus "MetaOCaml theory
  and implementation", https://arxiv.org/abs/2309.08207. Brackets,
  escape, run and cross-stage persistence. Scope extrusion through
  effects is caught by a *dynamic* check, a decade of practice that says
  types are not required.
- **LMS** (Rompf–Odersky, GPCE 2010, https://doi.org/10.1145/1942788.1868314):
  binding time lives in types (`Rep[T]`). That is global buy-in, which
  Klara principle 3 rejects as a default.
- **Amin–Rompf, "Collapsing towers of interpreters"** (POPL'18,
  https://doi.org/10.1145/3158140). *Stage polymorphism*: one evaluator,
  parametric in whether it interprets or generates (Pink's `lift`),
  collapses n interpreters into one compiler pass. This is the
  mechanism behind our collapse doctrine.
- **Futamura** (1971; reprint HOSC 12(4) 1999,
  https://doi.org/10.1023/A:1010095604496) and **Jones–Gomard–Sestoft**,
  *Partial Evaluation and Automatic Program Generation* (1993, free:
  https://www.itu.dk/~sestoft/pebook/). Mix equation, offline BTA,
  congruence (a value computed from a dynamic value is itself dynamic).
  Our grade join is the congruence rule extended with assumption sets.
- **Truffle/Graal.** Würthinger et al., "Self-optimizing AST
  interpreters", DLS 2012, https://doi.org/10.1145/2384577.2384587, and
  "Practical partial evaluation for high-performance dynamic language
  runtimes", PLDI 2017, https://doi.org/10.1145/3062341.3062381. PE of a
  self-specializing interpreter is the first Futamura projection in
  production. Assumptions fold to nothing and record a dependency.
  Deopt either discards the code or just transfers to the interpreter
  (studies/graal-truffle.md:29-30).
- **Self.** Hölzle–Chambers–Ungar: PICs (ECOOP'91, LNCS 512 pp. 21–38,
  https://bibliography.selflanguage.org/pics.html) and dynamic
  deoptimization (PLDI'92, https://doi.org/10.1145/143095.143114). A PIC
  is a *stable-argument* specialization cache, and deopt is what
  reconciles optimized code with source semantics.
- **Flückiger et al., "Correctness of speculative optimizations with
  dynamic deoptimization"** (POPL'18, https://doi.org/10.1145/3158137).
  Make assumptions explicit IR instructions (`assume`), and correctness
  of speculation becomes ordinary bisimulation reasoning. This is the
  template for our guard-soundness obligation.
- **Julia world age** (Belyakova et al., OOPSLA'20,
  https://doi.org/10.1145/3428275; extended version
  https://arxiv.org/abs/2010.07516). Juliette calculus: `eval`'d methods
  become visible only at the next top-level world raise, and this is
  what makes inlining sound in the presence of `eval`. Only 4–9% of
  packages bypass it. Our study adds the pitfalls of a single global
  epoch (design-decisions.md:722-761).
- **Incremental computation.** Acar–Blelloch–Harper, "Adaptive
  functional programming" (POPL'02). Hammer et al., **Adapton** (PLDI'14,
  https://doi.org/10.1145/2594291.2594324): a *demanded* computation
  graph with lazy, demand-driven repair. **Nominal Adapton** (OOPSLA'15,
  https://doi.org/10.1145/2814270.2814305) proves *from-scratch
  consistency*, which is exactly our cache-correctness statement. Names
  give stable identity across edits. Our content hashes are such names.
- **Build systems à la carte** (Mokhov–Mitchell–Peyton Jones, ICFP'18,
  https://doi.org/10.1145/3236774). A build system is a scheduler plus a
  rebuilder. Klara's expansion needs *monadic* tasks, because
  dependencies are discovered while resolving identifiers. It needs
  early cutoff, and it needs *constructive traces* (cloud-shareable,
  cross-fork) layered on verifying traces.
- **Racket.** Flatt, "Binding as sets of scopes" (POPL'16,
  https://doi.org/10.1145/2837614.2837620). The top level fails through
  hidden `top-level-bind-scope`, the fallback chain on re-expansion in a
  second namespace, and scope accumulation on repeated
  `module->namespace` re-expansion (studies/racket-rhombus.md:27, :67).
  Commit `ec881dfc54` notes scope-id nondeterminism.

## 3. Options and trade-offs

**3.1 Where binding time lives.**
(a) In types (LMS, MetaOCaml brackets, λ○/□). Statically safe, but a
global buy-in, and run-time re-expansion over open code is awkward.
(b) Dynamic only: syntax objects plus scope sets, with run-time
extrusion checks at `eval` (Racket, BER MetaOCaml's check). À la carte
and REPL-friendly, but errors come late.
(c) Dynamic core plus an optional ○/□ narrowing layer (the narrowing
doctrine). **Choose (c), shipping (b) in v1.** The narrowing obligation
applies: grade annotations reject programs or license residuals, and
they never change meaning.

**3.2 What "stable" means.**
(a) A lattice point with coarse invalidation (v0 `invalidate-stage!`).
(b) An assumption-set-indexed family. **Choose (b).** For two sources it
splits into two mechanisms, and keeping them apart matters for cost:
- *stable arguments*: guards at entry, PIC-style. A guard costs a check
  on every call and needs no invalidation.
- *stable world reads* (vars, macros, protocol tables, shapes):
  Assumption cells. They cost nothing on the hot path, and invalidation
  happens on write.

**3.3 Invalidation scheduling.**
Eager transitive invalidation (Julia's storm era) is one option. The
other is Adapton-style eager dirty-marking with lazy repair on demand.
**Choose lazy repair**, as already settled in language.md:180-186. Note
that Adapton marks dirty eagerly *along edges*, which costs O(edges
touched) rather than O(recompute).

**3.4 Deopt granularity.**
(a) Entry-only: a residual is a value behind a swap cell, and a failed
guard falls back to the generic program on the same input (the wandler
pattern).
(b) OSR with frame reconstruction (Self, HotSpot). On the JVM-hosted
tier we cannot reconstruct frames without our own emitter.
**Choose (a) for v1.** Loop headers act as safe points: they re-check
assumption validity and leave the loop, rather than swapping a frame
mid-loop.

**3.5 Collapse.**
(a) A separate AOT compiler, which drifts from the interpreter.
(b) Stage polymorphism: one evaluator, with grade as a parameter, so
collapse means specializing the evaluator with every assumption cell
declared static under a closed-world manifest. **Choose (b).**

## 4. Recommendation for Klara v1

**4.1 Grades.**
```
g ::= S | A | D          A ∈ P_fin(Cell),   S ⊑ A ⊑ A′ ⊑ D  for A ⊆ A′
g₁ ⊔ g₂ = union of assumptions; S is the unit; D absorbs
```
- A **literal**, a **content-hashed definition reached through a
  collapsed binding**, or a value derived only from S has grade S.
- A **world read** through a cell `c` has grade `{c}`. Its value is
  known at specialization time, and a write revokes it.
- An argument the caller marks `:stable` (or a profile reports as
  monomorphic) gets grade `{guard(arg, v₀)}`, an argument-guard pseudo-cell.
- Anything else is D. Congruence: an operation's result grade is the join
  of its inputs' grades, and control dependence on D makes the result D.

C-TOW-2's "re-expansion fires when staticness rises" becomes this: a
profile or a user annotation moves D to A, specialization is enabled,
and invalidation moves A back to D, which deopts. *Falsifier for 4.1*: a
profitable specialization whose validity condition is not a finite
conjunction of cell identities and argument predicates. Shape classes
are fine. A probabilistic validity condition is a candidate falsifier,
for example a specialization sound "with high probability", such as a
learned surrogate. That case belongs to aspect E's ε-grades, not here.

**4.2 Core forms** (on top of aspect A's core):
- `(quote-syntax e)`: a syntax value carrying scope sets. Content
  identity is α-canonical, never `=` on the datum.
- `(expand stx basis)` → `{:core stx′ :reads R :receipt …}`: the effect,
  reified. `R` lists the identifier resolutions, macro definitions and
  world cells consulted, each with the hash of the aspect read.
- `(eval stx [basis])`: expand, compile and run under `basis`, which
  defaults to the fiber's pinned basis. An identifier unbound in the
  basis is a scope-extrusion error.
- `(lift v)`: cross-stage persistence. It embeds a present value into
  code and is the stage-polymorphism hook. Function values are lifted
  by hash reference, never by copying a closure.
- `(specialize f statics [:stable ks])` → residual program value. **Its
  meaning is defined as s-m-n**: `(specialize f s)` ≡ `(fn [d] (f s d))`.
  The trivial closure is always a conforming implementation.
- `raise-basis!` (exists): the single visibility point for
  re-expansion.

**4.3 Invalidation protocol** (one graph, two visibility rules):
1. Nodes are `(kind, key)`. The kinds are `:expand` (key = α-canonical
   hash of syntax plus scope-set canonical form), `:analyze`, and
   `:specialize` (key = program hash plus hashes of static values). Each
   node stores `{result, reads: {cell → aspect-hash}, fuel, receipt}`.
2. **Macros are world definitions.** Transformers read the world only
   through the recording reader. A host-escaping read (deref of a host
   var) poisons memoization, as `effect!` does in stage.clj:55-60.
3. A write to cell `c` publishes the new value first and then marks
   dependents dirty, following CyclicAssumption's ordering. Nothing is
   recomputed at write time.
4. On demand, a dirty node re-verifies its reads (a verifying trace).
   If every aspect hash matches, it turns green and stops: early cutoff,
   with the *expansion output hash* as the cutoff aspect for macros.
   Otherwise it recomputes.
5. **Visibility:** recomputed `:expand` and `:analyze` nodes belong to the
   new world only. A fiber sees them after `raise-basis!`. Recomputed
   `:specialize` nodes go through the swap cell immediately, because
   they are equivalent by obligation O1/O2.
6. Bounded reoptimization: deopt-cycle detection per node at 15 cycles,
   a hard cap of 100 compiles, then the node is pinned to generic. Every
   deopt is poisoned against the cell or guard that lied.

**4.4 Content-addressing and caching across forks.** A constructive
trace stores `key ⊕ H(sorted reads)` → result in konserve. A fork
inherits its parent's cache by structural sharing. An entry computed in
fork F₁ is valid in F₂ iff every read's aspect hash matches F₂'s basis,
which is one lookup per read. Results are stored in **α-canonical
form**, with fresh scope ids and renames generated on retrieval. This
addresses Racket's scope-identity nondeterminism, because the cache
never stores raw scope ids. Scope ids should be derived from (parent
context hash, binder path) so that a fresh expansion of the same form
under the same basis yields identical canonical output.

**4.5 Staged path.**
M0, ship: hygienic `eval` with a basis, `quote-syntax`/`expand`, macros
in the world, recorded reads, lazy red-green with expansion-output
cutoff, trivial `specialize`.
M1: stage.clj residuals with real `depend!` on world cells, so only the
specializations that read a written cell die.
M2: stable arguments get guards, a PIC per call site (k≈4), entry deopt
via swap cells, and the reopt budget.
M3: the raster emitter as an optimizing tier, with profiles as W-ledger
evidence and Assumption cells folded into emitted code.
M4: collapse, which declares a manifest's cell set static, specializes
the stage-polymorphic evaluator, and records the closed-world
assumptions in the artifact. `eval` inside a collapsed artifact falls
back to the embedded expander and interpreter, at a size cost (jank and
Truffle precedents, language.md:226-229).

## 5. Obligations and falsifiers

| # | Obligation | Status | Falsifier / evidence |
|---|---|---|---|
| O1 | specialize-then-run ≡ run (s-m-n) | **Holds** for the trivial specializer (by definition); **Conj** for PE residuals | a residual and the generic program disagree on a corpus input under differential testing |
| O2 | Guard soundness: guards(x) ∧ cells valid ⇒ residual(x) ≡ generic(x); guard failure falls back losslessly on the same input | **Open** (method: Flückiger-style explicit `assume` in the residual IR, with bisimulation) | a residual that folds a world read without registering its cell; a fallback that re-runs an effect |
| O3 | From-scratch consistency: cached or repaired expansion ≡ fresh expansion under the same basis | **Open**; **v0 currently falsifies it** (E0) | E0 itself; any read the expander makes without recording it |
| O4 | Read-set completeness for transformers | **Conj**: holds by policy, not as a theorem, because macros can call the host | a macro whose output depends on an unrecorded host read. Mitigation: rotating 1/32 re-expansion check (rustc) |
| O5 | α-determinism: same form under the same basis gives the same canonical expansion | **Holds** for v0 def hashes (verified); **Open** for cross-fork scope ids | two forks producing different canonical hashes for the same (form, basis) |
| O6 | Basis isolation: no fiber observes re-expansion before it raises | **Holds** for v0 pinned reads (world.clj:92-110); **fails** for host-emitted code (defs.clj:211-214) | a running closure picking up a redefinition without a raise |
| O7 | Deopt-loop freedom | **Conj** (Truffle budget numbers) | a workload cycling between specialize and deopt inside the budget forever, without pinning |
| O8 | Cross-fork cache soundness | **Conj**, conditional on O4 plus collision resistance | an entry valid by read hashes but wrong in F₂, which would mean O4 is broken |
| O9 | Collapse adequacy: artifact ≡ dynamic program on runs where the manifest's cells are never written | **Open** | a collapsed artifact diverging on a run that respects the manifest |
| O10 | Stage polymorphism: one evaluator serves interpretation and residual generation | **Conj** | a semantic fix that has to be made twice (interpreter and specializer) |
| O11 | Grades never change meaning (narrowing doctrine) | **Conj** | removing a `:stable` annotation changes an output |
| O12 | C-TOW-3 is complete | **Open**; read-set completeness (O4) and basis isolation (O6) are candidate 4th and 5th conditions | as stated in spine.md:155 |

## 6. Smallest implementation experiment (on v0, ~150–250 LOC, new namespace)

**E1: macros in the world, with recorded expansion reads.**
1. Store transformers as world entries `{:macro f :def {:shallow … :form …}}`.
2. Give `resolve-id` and macro lookup a dynamic `*reads*` collector that
   records `[:macro sym shallow-hash]` and `[:binding sym scopes]`.
3. `defv!` merges expansion reads into `:deps`, together with the
   *canonical expansion hash* as the aspect recorded for each macro
   dependency.
4. `invalidate` on a macro re-expands its dependents and compares the
   canonical expansion hash. Equal hashes give cutoff (green).
   Otherwise the dependent is re-analyzed, and the existing interface
   firewall continues.

**Pass criteria:**
(i) E0 yields `(f 3) = 9` after redefine plus invalidate.
(ii) A refactoring of `twice` with identical output leaves `f` green via
cutoff.
(iii) The same macro redefinition in a `w/fork` leaves the parent's `f`
at 6.
(iv) Inside `with-basis` the old `f` is observed until `raise-basis!`.
(v) A cache keyed on the bare form reproduces the scope collision, and
the α-canonical key does not.
(vi) Measure re-expansion work against whole-file re-expansion on the
v0 showcase corpus.

**E2** (optional, same session): wire `stage/depend!` to world reads,
so redefining a var drops only the stage entries that read it. Count
entries dropped against `invalidate-stage!`.

## 7. Questions for Christian

1. **Is "stable" a stage or an assumption?** I propose treating stable
   as "dynamic, plus a named set of revocable facts". In your PPL terms,
   it is like conditioning a compiled inference program on observed data
   and keeping the data's hash as a guard. Do you accept the split of
   C-TOW-2 into stage level × assumption set? Do you see a case, perhaps
   a probabilistic one, where validity is not a finite conjunction of
   facts?
2. **May macros perform arbitrary effects?** Examples are reading a
   schema file, querying datahike, or calling an LLM (Template Haskell's
   `runIO`, F# type providers). If they may, read-set completeness breaks
   unless every such effect goes through the expansion handler, which
   records it as an external input with a hash ("volatile task" in
   build-system terms). Do we require that, or accept trust plus rotating
   verification?
3. **When does running code see a re-expansion?** The Julia answer is:
   only at explicit basis raises, which gives snapshot consistency. The
   spindel answer is: some fibers subscribe and re-raise reactively, which
   gives liveness, as when a REPL-attached simulation picks up an edited
   model. I propose raises by default and reactive raising as an opt-in
   spin. Is that the right default for simulation work?
4. **Typed staging in v1, or later?** λ○/□ or environment classifiers
   would give static scope-extrusion safety, at the cost of a typing
   layer. I recommend dynamic checks in v1 and typed staging as a
   narrowing layer.
5. **Is entry-only deopt acceptable for v1?** Long-running loops would
   check assumptions at loop headers rather than swapping frames
   mid-flight (no OSR until our own emitter).
