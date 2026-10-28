# H — metacarp, Veit Heller, and what Klara should take (research note, 2026-10-27)

Status markers as in B: **Holds**, **Conj**, **Open**. Paths are relative to
`Development/`. Sources: `metacarp-upstream` at `512ef81` (v0.0.3),
`metacarp` (Christian's fork, branch `carpaccio-library-abi`),
`research/memory-region-facts` (`5e5130d`), `carpaccio` at `2a91410`, and
GitHub, read-only, on 2026-10-27.

## 0. Disagreements first

1. **The premise does not match what is on GitHub.** Veit's RFC is
   [cyberwitchery/metacarp#74](https://github.com/cyberwitchery/metacarp/issues/74),
   and it contains **no pointer to a macro type system**. Christian has
   **no comments on #74**. He is @-mentioned once, crediting #50. The
   macro-typing pointer is somewhere else: in
   [PR #37](https://github.com/cyberwitchery/metacarp/pull/37) and in
   `metacarp-upstream/carp-ct-types/README.md`. Christian's written exchanges
   with Veit are on PRs #29, #31, #114 and #116. If the macro pointer came up
   in a private channel, this note assesses the pointer the repository itself
   gives.
2. **The thread has a norm Klara must respect, and it matters more than any
   technical point.** Veit blocked a participant (M-Tesla) for posting agent
   output on #74. He wrote: "I would like to prefer to keep the design space
   light on LLMs … I don't want to outsource our thinking", and "using agents
   to develop ideas is fine, relaying them unfiltered is not." This note is
   agent output. §4 is a list of *positions to check and then rewrite in your
   own words*. It is not text to paste.
3. **v1 §13 mischaracterizes metacarp** (`01-core-v1.md:334`). It says
   "metacarp's type-checked macros point the same way" as Lean's elaborators.
   They do not. metacarp types a macro *as a program over forms*. It gives
   the macro no type information about the object program, and the macros
   stay unhygienic (`carp-expand/README.md`). This is a different rung of
   the ladder (§2).
4. **"Ownership as Klara's static layer" overstates what transfers.** Most
   of metacarp's affine machinery, and most of its bugs, plan the
   *deallocation of data*. Klara's data is aliasable and GC-hosted. Only the
   rules about *authority* transfer: borrow-checking, places, moves into
   closures, and one authority for every settlement. That is a much smaller
   surface. It is good news for RFC 0001's static layer, but the cost data
   from metacarp mostly does not apply (§3b).

## 1. Veit's RFC: #74, "planned memory effects, noalloc, and scoped arenas"

Opened 2026-09-26, labelled `rfc`, open, last activity 2026-10-09.

**Goal.** PR #60 gave every compiler primitive a `CoreMemoryManifest`. It
took Christian's #50, with unannotated primitives made `Unknown`. Nothing
reads the manifests, and most heap events in emitted code are invisible to
them. Four places currently decide allocation and freeing "more by
coincidence than by construction":
- the ownership plan;
- `BackendLower`, which frees hoisted literals, `_` payloads, temporaries and
  echo results;
- the C renderer, which does every allocation plus two frees;
- C template text.

The LLVM backend has already drifted from the C one (#79: `field-set!`
leaked the displaced value). No gate checks leaks in emitted programs, and
`noalloc` cannot even be stated.

**Design**, in nine parts:

1. Every heap event becomes a primitive call with a manifest: array storage
   alloc and free, closure environment alloc and free.
2. **The plan owns every free.** `field-set!` becomes a `set!` on a field
   projection. `Temporary` deletes become placed actions. New invariant:
   "`BackendLower` places what the plan schedules and never schedules
   anything itself."
3. Both backends print through one hook, `carp_alloc`/`carp_realloc`/`carp_free`,
   which counts all three events.
4. One new effect, `Store [Global | Argument i]`: writing an owned value into
   memory the function did not create.
5. A new library, `carp-memory`, computes transitive per-specialization
   summaries after lowering. It runs SCCs through `carp-graph`, takes the
   least fixpoint over effect sets, maps argument-relative facts through each
   call site, and records a witness (the callee chain) for each effect.
6. Contracts at opaque leaves are metadata, so reference Carp still compiles:
   `(meta-set! Pointer.free "memory" '[(free 0)])`. A contract on a visible
   body is an error. Upstream Core gets its contracts from an overlay file.
7. `(noalloc f)` is a compile error that names the call chain. `--memory`
   emits JSON.
8. Runtime falsification: a contract observer snapshots the counting runtime
   around each contracted leaf in CI, and a leak gate checks each emitted
   program. "Observation only falsifies; a contract stays trusted where no
   test reaches it."
9. A program-wide swappable allocator, then **scoped arenas**. `alloc`
   follows the current allocator, while `realloc` and `free` follow the
   pointer. A managed result is copied out with the parent allocator, and a
   `Ref` result is rejected. No escape by store, and no `Unknown` calls
   inside the scope.

**Out of scope:** "allocator provenance in types (`Own alpha`, `Cap alpha` in
the replikativ notes) … would make a different language from upstream carp."
That is Christian's `docs/allocator-parametric-memory.md` on
`research/memory-region-facts`.

**Open questions:** closure calls are `Unknown` (would a flow analysis pay?);
symbolic extents or only counts; pools and fixed buffers; implicit or
explicit copy-out; the surface name.

**Discussion so far:** two comments, both Veit's. He answered M-Tesla, whose
comment has been deleted, with five points. The two that matter here:
- the proposal violated the central invariant: "the ownership plan must own
  every free";
- "there is a completely untouched fundamental problem of stores into
  externally rooted bindings."

He then blocked M-Tesla. **No design responses yet.** The two problems
Veit named are still open, and they are the natural entry points (§4).

**Lineage worth knowing.** `research/memory-region-facts` (2026-08-29) already
prototyped the core of #74: structured primitive effects, transitive
specialized summaries, foreign memory contracts, and a contract observer.
Veit's RFC adopts the summary and contract mechanism and drops allocator
provenance. On #29 he stated his acceptance criteria: he declined to take
"new syntax the reference does not have", anything "descriptive only, no
consumer", and anything with "no in-repo consumer". Every proposal in §4 is
shaped to pass these criteria.

## 2. The macro type-system pointer, verified and assessed

**Source, verified.** Chun Yin Chau and Lionel Parreaux, *The Simple Essence
of Boolean-Algebraic Subtyping: Semantic Soundness for Algebraic Union,
Intersection, and Negation Types*, POPL 2026, PACMPL 10(POPL), pp. 1353–1382
([paper page](https://cse.hkust.edu.hk/~parreaux/publication/popl26/),
[POPL listing](https://popl26.sigplan.org/details/POPL-2026-popl-research-papers/49/The-Simple-Essence-of-Boolean-Algebraic-Subtyping-Semantic-Soundness-for-Algebraic-U)).
It reframes MLstruct's BAS (Parreaux and Chau, OOPSLA 2022) with five
families of characteristic Boolean homomorphisms, and shows subtyping
NP-hard even without recursive types. The decision procedure stays
exponential in the worst case. Neither paper is in Zotero yet.

**Two implementations in metacarp, at different depths.**
- `carp-ct-types` + `carp-ct-infer` (on main, opt-in, unwired).
  - Only the shape homomorphism `H` exists, a bitmask over a tag tree.
  - It reports only provable impossibilities: an operation is rejected when
    what it requires, intersected with what it may receive, is `⊥`.
  - Validation: an evaluator oracle over 39 builtins found 0 too permissive
    and 0 too strict. A mutation run caught 874 of 874 seeded errors. On
    reference Core, 0 of 289 definitions are rejected, but only 129 of them
    contain anything decidable.
  - Its README says it is "roughly a third of the way to what the paper
    describes".
- PR #37, `carp-ct-typecheck` (open since 2026-09-13, updated 2026-10-26, no
  review yet).
  - Full MLstruct `constrain`: arrows, `car`/`cdr` fields, recursive types
    and negation.
  - A macro is typed as a function from forms to forms. A macro call is
    typed as its expansion, which is expanded at check time.
  - `docs/bas-calculus.md` gives a soundness sketch that reduces to
    MLstruct+ with named obligations O1–O6.
  - Results: 251 of 276 Core definitions check in about 65 ms, and the
    checker found **3 real Core bugs** (Carp #1600, #1604).
  - Costs: without a pruning step, 13 definitions do not finish within a
    minute. One arrow per builtin means no overloads. User predicates do not
    narrow. `append`'s two-variable kind constraint cannot be expressed.

**Assessment: moderately helpful, for one rung of Klara's ladder only.**

v1 §13 and v2 §6 set up a ladder:
1. hygiene, always;
2. a declared input grammar and binding interface;
3. output checked as well-formed core;
4. typed code, opt-in, BER MetaOCaml style.

BAS answers a question that sits *between 2 and 3*: given the input grammar,
can the macro body itself go wrong? It does not answer what v2 §6 actually
needs:
- **Hygiene and binding structure.** BAS has no notion of scope. Carp's
  expansion is unhygienic, and the README says symbol identity "is dynamic
  because expansion is unhygienic." The relevant literature is Herman and
  Wand's typed hygienic macros, Stansifer and Wand's Romeo, and
  Racket/Turnstile scope sets. Klara already chose scope sets.
- **Typing of the generated code.** BAS types the *meta* program, not the
  object program. Scope extrusion and closedness (`close`/`run`) are
  MetaOCaml questions. They are untouched.
- **Clojure's core library under one arrow per function.** `conj`, `get`,
  `into` and `assoc` are deeply overloaded and multi-arity, and Clojure
  macros branch on user predicates constantly. Both are exactly where #37
  gives up. Of #37's 15 direct failures in Core, 3 come from user predicates
  and 4 from `eval` results used as data. Expect a higher share on
  `clojure.core`.

**What Klara should take from it:**
- **Grammar as type.** A declared input grammar can be compiled into a BAS
  type over syntax: tags, `car`/`cdr` fields, unions, recursive variables.
  `clojure.core.specs` already writes grammars for `defn`, `let` and `fn`.
  This gives rung 2½: *under its declared grammar, the extension's body
  raises no shape error*. It is a checked claim in v2 §7's sense, cheap and
  free of false positives.
- **"Report only provable impossibilities, map unknowns to `⊤`."** This is
  the right discipline for an untyped core. It is the checked-claims
  contract applied to the meta level.
- **The validation method more than the calculus:**
  - an oracle that checks the builtin table *against the evaluator, in both
    directions*;
  - mutation testing over a corpus;
  - a coverage line ("a pass that reports nothing because it examined
    nothing is otherwise indistinguishable from a clean result").

  Klara's corpus should adopt all three for every checker it ships.

**What not to take:** principal inference as the reason to adopt BAS.
Klara's checks are opt-in and local. NP-hardness, together with Veit's
measured need for a pruning step, argues for running BAS only on declared
grammars, not on whole programs. **Verdict on the pointer:** it is a sound,
well-executed checker for meta-program *shape* errors. It is not a type
system for syntax extensions, and it does not change v2 §6.

## 3. metacarp's lessons for Klara

### (a) Macro typing vs Klara's syntax extensions

metacarp's expander is a bytecode-compiled compile-time VM
(`carp-ct-eval`, PR #38). Its macros are unhygienic and fixed-arity or rest.
A macro body is compiled once at definition, and a call runs that code
(`carp-expand/README.md`). `diff-expansion.sh` requires identical observable
expansion against the reference compiler.

Take:
- the expansion-parity gate;
- **compile macro bodies at definition time.** This complements spindel's
  tracking engine: cache keys on the CodeId of the expander.
- Carp #1603, `eval-form`, shows a concrete failure mode that Klara's value
  kinds already prevent: `eval` returns a closure where a form is expected.
  Klara separates datum, syntax and code (v2 §6), which is the structural
  fix. Keep it.

### (b) Ownership and affinity as the static narrowing layer for authority

**What metacarp has.**
- A flow-sensitive borrow check threads a moved set plus per-binding
  origins through evaluation order, and joins branches by union of moves
  (`carp-ownership/README.md`).
- Places are a root plus field, index, slice and deref projections, with
  `places-overlap?` proving separation conservatively (#64).
- Capture of an owned value is a move. Calling a closure borrows it. A
  consuming use inside a closure body "is rejected because the closure can
  run more than once" (`carp-ownership.carp:1718-1726`).
- In the fork, `Ref` stays one type, and shared vs unique is an *effect* in
  the plan and in foreign contracts, not a type (`metacarp/docs/semantic-delta.md`).

**What transfers to RFC 0001:**
1. **The multi-shot rule already exists.** "A consuming use inside a closure
   is rejected because it can run more than once" is exactly fork-resume's
   rule: an authority captured by a resumable continuation must be *split*,
   not moved. Klara needs the same check with "split" as the escape hatch
   that metacarp lacks.
2. **Partition is a places problem.** `partition-fork!` requires disjoint
   *and exhaustive* subsets. metacarp proves disjointness only. Exhaustiveness
   is new and is Klara's to add.
3. **Authority as an effect, not a type.** metacarp keeps `Ref` single and
   puts the mode in summaries. That fits Klara's untyped core: the static
   layer is a summary analysis over core, not a type system.
4. **"The plan owns every free" becomes "one authority owns every
   settlement."** #74's founding observation: four sites decided heap
   events, and the second backend drifted. That is AU7's risk exactly. If
   the dynamic checker, the static layer and a backend can each settle an
   authority, they will diverge. Settlement must be one IR-visible operation
   that only the plan schedules.

**Costs and limits seen in metacarp.**
- The bug history is overwhelmingly about *data* deallocation: #55, #72,
  #79, #104, #106, Carp #1576 (leak on `break` inside `if`), and invariants
  9, 12 and 14 in `docs/invariants.md`. Klara pays none of this.
- Limits that *do* carry over:
  - lifetimes are relations in concrete summaries, not quantified;
  - strict foreign collection is whole-root, not field-sensitive;
  - built-in mutation is not strict-checked, because "enabling that now
    would reject established disjoint-field patterns" (`semantic-delta.md`).
    Precision gaps become rejections of correct code. For an *opt-in* layer
    that erases checks, a rejection there must fall back to the dynamic
    check, never become an error.
- Closures are affine whenever they may hold an environment (B §0.5). Klara
  computes copyability from captures instead (B §4.7). Keep Klara's default:
  in a GC host, metacarp's default would make every closure non-forkable.

### (c) Memory-effect manifests and region facts vs Klara's memory model

The correspondence is close.
- An **arena scope** is an island (B §4.8).
- **Copy-out** is freeze at the island boundary. carpaccio's `snapshot` is
  the O(n) version (O1 violation).
- **No escape by store** is the snapshot-fork rule: a fork body may not
  write into parent-rooted state except through the overlay.
- **`noalloc`** is a static proof of a zero memory budget, the hard budget
  component of RFC 0001.
- **Witness chains** are receipts.
- **The contract observer** is the trust ledger's "property-tested ⇒
  guarded only" rule.

Veit's unsolved "stores into externally rooted bindings" is *the same
problem* as Klara's AU4 (snapshot fork: no parent write visible across the
boundary), seen from the inside.

Take:
1. **Summaries as a least fixpoint over SCCs, with argument-relative facts
   mapped through call sites.** This is the shape of Klara's authority
   summaries. spindel's tracking engine can host it.
2. **Contracts as s-expression metadata that the reference ignores.** This
   is how Klara's L0/L1 code can carry contracts without changing meaning.
3. **Allocators as algebras of an effect theory**
   (`allocator-parametric-memory.md`). Veit ruled this out for metacarp, so
   Klara is its natural home. An allocator is a handler instance (RFC 0002)
   whose facts (reclamation, mobility, capacity) license the static rules.
   Arenas, pools and fixed buffers are the "scoped allocators beyond arenas"
   question in #74, answered by "the handler's facts decide which rules
   apply".

### (d) Self-hosting and bootstrap discipline vs ring 5

metacarp's discipline:
- byte-identical C of **gen 2 vs gen 3**, not gen 1 vs gen 2, because gen 1
  comes from the reference compiler;
- gen 2 built as strict C99 with `-Werror=typedef-redefinition`;
- gen 2 runs the reference suite, the expansion diff, ASan, and a leak check
  at 0 bytes;
- a seed compiler from an earlier passing build, with the reference compiler
  used only where it is the thing compared against
  (`scripts/check-fixed-point.sh`, README §Self-hosting).

Christian's bundle adds `manifest.properties` with both revisions and the
SHA-256 of the compiler C (`metacarp/scripts/build-bootstrap-bundle.sh`).
Upstream did not take it.

For `bootstrap.md` ring 5:
1. **The fixpoint is necessary, not sufficient.** metacarp gates the
   fixpoint *and* the full suite through gen 2. Ring 5 already says "fixpoint
   hash + full corpus". Keep both.
2. **Determinism is an obligation on the emitter.** metacarp's invariant 4
   ("allocation order is part of the ABI") and invariant 26 (two
   hand-synchronized Core file lists) are both threats to a hash compare.
   Klara leaves the iteration order of unordered collections unspecified and
   randomizes it in test mode (v2 §3). So **the compiler must never iterate
   an unordered collection into output**, or the fixpoint hash breaks under
   test mode.
3. **A seed is a trust root.** metacarp keeps an independent reference
   compiler. That makes diverse double-compiling possible (Wheeler 2009). Klara
   has one too: compatibility mode on Clojure, or v0/sci. Ring 5 should name
   DDC as the check that a content-addressed seed alone does not give.

### (e) The native/LLVM tier

- `carp-llvm-backend` lowers the same `BackendModule` as the C backend and
  has reached reference-suite parity.
- The ORC session JIT runs a warm cell in 62.8 ms, against 382 ms for the
  emit-C/clang path. carpaccio uses the C path, at 552–581 ms per
  replacement (`carpaccio/docs/architecture.md`).
- The drift in #79 shows the cost of two lowerings, and #74's fix is to
  move every decision before the fork into two backends.

For Klara:
- **No Klara LLVM backend.** The native tier is affine islands compiled
  through metacarp, via carpaccio.
- The owned runtime of ring 6 stays Wasm.
- Gate R2 (≤ Clojure + max(5 ms, 10 %)) **cannot** be met by any native
  path measured here. Native compilation therefore stays off the critical
  path of redefinition, consistent with v2 §6.
- If the Effekt-runtime port (G §LLVM, option 2) is ever attempted, it goes
  into metacarp's LLVM backend. It is Veit's call.

## 4. Collaboration: overlap, sharing, differences, questions

**Where the goals overlap.** Both projects need:
- one authority per lifecycle event;
- transitive effect summaries with witnesses;
- checked contracts at opaque leaves, falsified by observation;
- a scope that nothing escapes.

#74 solves this for bytes inside a native compiler. RFC 0001 solves it for
authorities inside a forkable runtime. carpaccio is where the two meet.

**What to share, ranked by Veit's acceptance criteria:**
1. **The contract vocabulary as data.** #74's `memory` grammar is already
   s-expressions, and carpaccio already reads ownership as EDN over CBOR.
   Propose that the overlay file for upstream Core contracts (which #74
   plans anyway) is versioned and machine-readable. carpaccio and the Klara
   seam would consume it as a second consumer. The first consumer is in the
   repository: the summaries and the observer.
2. **The `--memory` JSON / session query.** carpaccio consumes it, and
   Klara's B §4.8 seam uses it to decide which island calls may allocate.
   Veit has already planned this output.
3. **Corpus and validation method, not code.** Share:
   - the expansion-parity corpus;
   - the oracle and mutation discipline of `carp-ct-infer`;
   - fixtures for the leak gate.
4. **Not the IR.** metacarp's IR is typed, monomorphized and C-oriented, and
   Klara's core is untyped CBV with effects. The shared interface stays at
   surface forms plus the session protocol, where carpaccio already sits.

**Where the two genuinely differ:**
- **Fidelity to upstream Carp.** For Veit this is a constraint: no new
  syntax, no allocator types. Klara is a new language.
- **Memory.** Klara is GC-hosted with aliasable data and multi-shot
  continuations. metacarp is owned and single-shot.
- **Process.** Veit wants human-authored design discussion.

Allocator provenance, authority splitting and fork are Klara's to design.
Bringing them to #74 as requirements would be off-topic.

**Questions and positions for #74.** Check each against the code before
posting.

1. *Stores into externally rooted bindings.* Classify a store target by its
   `OwnershipPlace` root (#64), not by binding: the root is inside the scope
   iff the scope's binder set contains it. Then a callee's
   `Store (Argument i)` maps to the caller's **place**, so
   `(Array.push-back! &(.items outer) x)` is caught even though `outer` is
   only reached through a projection. Does `Store`'s target need to be a
   place rather than `Global | Argument Int`?
2. *Deletes inside the scope.* If arena-born containers later skip their
   deleters, a value moved in from outside and stored into one would leak at
   reset. Should the summaries track "adopts an outside owner" separately
   from `Store`, so that the elision can be refused exactly there?
3. *Copy-out.* Argue for an **explicit** form. carpaccio's O(n) `snapshot`
   is the cost users must see. An implicit deep copy at scope end is the
   same mistake in a different place.
4. *Closures created inside an arena.* Is a closure result a "managed result
   copied out by its copier"? Its environment may hold pointers to arena
   data that `Function.copy` copies only shallowly.
5. *Closure calls as `Unknown`.* Rejecting them makes higher-order code
   (`Array.reduce` with a lambda) unusable in arenas. A minimal refinement:
   a lambda literal let-bound or passed in the same body has a visible
   summary. That is 0-CFA restricted to literals. How much of Core's
   string code would that recover? Measure before deciding.
6. *Thread-local current allocator.* What does an arena mean across a
   callback into C that re-enters Carp, the case carpaccio hits with Panama
   upcalls?

**Where Klara should defer to Veit (designed holes he owns):**
- delete planning and placement, plus the plan/`BackendLower` invariant;
- the arena static rules;
- the C-ABI, layout and mangling;
- LLVM lowering and the JIT;
- the builtin fact tables and soundness obligations of BAS;
- judgments about reference fidelity.

In Klara's docs, each of these is a named interface (the island contract,
the memory-summary query, the `defshared` layout) with "owner: metacarp
upstream" and no Klara-side redesign.

## 5. Obligations and falsifiers for what Klara adopts

| Id | Claim adopted | Status | Falsifier / check |
|---|---|---|---|
| H1 | One authority per settlement: only the plan schedules settle/consume; the dynamic checker and backends place, never decide | Open | differential trace test: the dynamic-only and static-erased runs settle in the same order (extends AU7); a second backend that settles anything the plan did not schedule |
| H2 | Consuming an authority inside a resumable closure or continuation is rejected unless it is split (metacarp's run-more-than-once rule, plus split) | Conj | adversarial suite: an authority captured by a two-shot `choose` continuation and consumed in both branches |
| H3 | Partition proofs reuse place disjointness and add exhaustiveness | Open | a partition with disjoint but non-covering parts accepted by the static layer |
| H4 | Static-layer imprecision never rejects a program the dynamic layer accepts (fall back, don't fail) | Conj | the corpus with the layer on and off: any program that runs dynamically but is rejected statically |
| H5 | Grammar-as-BAS-type checks of extension bodies report no false positives on correct code | Conj | mutation and oracle runs as in `carp-ct-infer`; one correct `clojure.core` macro rejected under its `core.specs` grammar falsifies it |
| H6 | BAS cost is bounded on declared grammars | Open | any `clojure.core` macro whose check exceeds 100 ms with the pruning step |
| H7 | The compiler never iterates an unordered collection into output (fixpoint stable under test-mode randomization) | Open | ring 5 fixpoint hash differs between two runs with randomized iteration |
| H8 | Contracts at opaque leaves are observation-falsifiable; untested contracts stay at "trusted" in the ledger, never "checked" | Holds in design (#74 §8) | a ledger entry marked checked with no observer coverage |
| H9 | Native compilation never sits on the redefinition critical path | Holds (measured: ≥ 62.8 ms warm JIT vs R2's 5 ms floor) | a release path where R2 waits on clang or ORC |
| H10 | The contract vocabulary is shared as versioned data with ≥ 2 consumers (metacarp summaries, carpaccio/Klara seam) | Open | the vocabulary forks between the projects within one release |

**Next actions:**
- Add Chau & Parreaux (POPL 2026), MLstruct (OOPSLA 2022), Romeo and Herman's
  typed hygienic macros to Zotero.
- Correct `01-core-v1.md:334`.
- Write the #74 comment yourself, starting from §4 Q1. It answers the problem
  Veit named and is still open.
