# G. Effekt, selective CPS, and Klara's continuation strategy (2026-10-27)

Input for Christian's follow-up with the Effekt author and for the v2 decision
on JVM continuations (Codex review §2, "Continuations are the missing
architecture experiment"). Status markers as in `01-core-v1.md`: **Holds**,
**Conj**, **Open**. "Verified" means checked against the paper PDF, the
publication page, or the Effekt source on GitHub (`effekt-lang/effekt`, branch
`main`, read 2026-10-27; latest release v0.82.0, 2026-09-28). Everything else
is marked.

**Person (verified).** Jonathan Immanuel Brachthäuser, University of Tübingen
(PL Center / Software Engineering). Full Professor since December 2025, Junior
Professor from November 2021 (pl.cs.uni-tuebingen.de/team/brachthaeuser). His
closest collaborators on compilation are Philipp Schuster and Marius Müller,
with Klaus Ostermann. He also co-authored Koka's first evidence-passing paper
(Xie, Brachthäuser, Hillerström, Schuster, Leijen, *Effect Handlers,
Evidently*, ICFP 2020). The Koka/Effekt comparison below is therefore a
comparison inside one research conversation, not between rival camps.

## 1. What Effekt is (verified)

**Lexically scoped handlers, effects as capabilities.** *Effects as
Capabilities: Effect Handlers and Lightweight Effect Polymorphism*
(Brachthäuser, Schuster, Ostermann, OOPSLA 2020, doi 10.1145/3428194). A
handler binds a capability, a value in lexical scope. An effect operation is a
method call on that capability, so `perform` is a call on a known receiver,
not a search of the dynamic context. Semantics is given by translation to
System Ξ, a calculus in explicit capability-passing style. To keep this
effect-safe, *all functions are second-class* in that paper: they can be
passed but not returned or stored, so a capability can never outlive its
handler.

**Contextual effect polymorphism (verified term).** The term appears in
*Effects, Capabilities, and Boxes: From Scope-based Reasoning to Type-based
Reasoning and Back* (Brachthäuser, Schuster, Lee, Boruch-Gruszecki, OOPSLA
2022): "Blocks can use all effects from the context they were defined in …
This form of polymorphism is called contextual effect polymorphism." A block
argument `{ f: () => A }` mentions no effects. It closes over whatever
capabilities its definition site holds, and those are handled there, not by
the higher-order function that calls it. There are no effect variables. The
cost the 2022 paper names: closing over capabilities is invisible in types,
which "hinders reasoning about its purity".

**Second-class functions and boxing.** The 2022 paper (System C) brings back
first-class functions. `box` turns a block into a value whose type records its
*captures*, e.g. `() => Nothing at {exc}`; unboxing is allowed only where all
captured capabilities are in scope (Effekt tour, "Captures"). The tour
distinguishes effects ("an open demand", handled by the caller's context) from
captures ("a fixed capability", fixed by the defining scope). A function that
requires `() => Unit at {}` rejects a closure that captures `io`. That is an
authority check written as a type.

**Compilation lineage (titles and venues verified).**

| Paper | Venue | What it contributes |
|---|---|---|
| Brachthäuser, Schuster, Ostermann, *Effect Handlers for the Masses* | OOPSLA 2018 | Java library: "a type selective CPS transformation via JVM bytecode transformation", delimited continuations on top, handlers on top of that |
| Schuster, Brachthäuser, Ostermann, *Compiling Effect Handlers in Capability-Passing Style* | ICFP 2020, doi 10.1145/3408975 | λCap → STLC in **iterated CPS**, monomorphized by stack shape; a second-class sublanguage λλCap gets a **staged** translation that provably removes all handler abstraction (up to 409× in their benchmarks) |
| Schuster, Brachthäuser, Ostermann, *Region-based Resource Management and Lexical Exception Handlers in Continuation-Passing Style* | ESOP 2022 | regions + control in one CPS framework |
| Schuster, Brachthäuser, Müller, Ostermann, *A Typed Continuation-Passing Translation for Lexical Effect Handlers* | PLDI 2022, doi 10.1145/3519939.3523710 | first CPS translation of lexical handlers into pure System F; "typed lexical effect handlers do not need the full power of multi-prompt delimited control"; no runtime labels |
| Müller, Schuster, Starup, Ostermann, Brachthäuser, *From Capabilities to Regions: Enabling Efficient Compilation of Lexical Effect Handlers* | OOPSLA 2023, doi 10.1145/3622831 | **lift inference**: infers how far each effect must be lifted through handlers, by translation to a region calculus with subregion evidence; feeds iterated CPS (MLton backend) |
| Müller, Schuster, Brachthäuser, Ostermann, *Back to Direct Style: Typed and Tight* | OOPSLA 2023, doi 10.1145/3586056 | typed translations CPS → direct style (with control operators) and back; one-sided inverses in general, full inverses on trivial control flow |
| Muhcu, Schuster, Steuwer, Brachthäuser, *Multiple Resumptions and Local Mutable State, Directly* | ICFP 2025, doi 10.1145/3747529 | the **LLVM backend** and its runtime (below) |
| Gaißert, Bolz-Tereick, Brachthäuser, *Tracing Just-in-time Compilation for Effects and Handlers* | OOPSLA 2025, doi 10.1145/3763085 | RPython meta-tracing JITs for Eff, Effekt and Koka over a common bytecode |
| Voigt, Schuster, Brachthäuser, *Dynamic Wind for Effect Handlers* | OOPSLA 2025 | entry/exit actions under resumption |
| Müller et al., *Compiling with the Sequent Calculus* | TOPLAS 2026 | (not read) |

Naming discrepancy: effekt-lang.org lists the ICFP 2020 paper as
"Capability-Passing Style for Zero-Cost Effect Handlers". The PDF and the DOI
record say *Compiling Effect Handlers in Capability-Passing Style*. Cite the
latter.

**The LLVM runtime (verified in the paper and in `libraries/llvm/rts.ll`).**
- Segmented stacks: a meta-stack of stack segments. Each `reset` allocates a
  fresh segment and a **prompt with a stable heap address**, and the segment
  points back to that prompt.
- `shift` follows the prompt pointer straight to its segment, so there is
  **no handler search**: capture and resume are O(1) for one-shot use.
- **Garbage-free reference counting** (Perceus-style). A continuation is
  copied only when it is resumed while shared, so multi-shot costs a stack
  copy and one-shot costs nothing.
- Local mutable variables live in stack segments, addressed as (prompt,
  offset). A multi-shot resume therefore gives each copy its own state, so
  state is backtracked.
- The design builds on Lexa (Ma, Ge, Lee, Zhang, *Lexical Effect Handlers,
  Directly*, OOPSLA 2024), whose direct stack pointers rule out multi-shot.
- Limitation stated in the paper: continuations are not reentrant (a
  continuation cannot be resumed concurrently). The paper's Fig. 17 shows the
  old JS backend scaling non-linearly with nesting depth because of handler
  search; the LLVM backend fixes that.

**How Effekt decides where continuations are needed (from source; not a paper
claim).** Christian's phrase "fairly smart at inferring breakpoints and doing
CPS with LLVM IR" needs adjusting:
- Effekt core has explicit `Reset`, `Shift(prompt)` and `Resume`. Prompts are
  lexically bound values, which is the PLDI 2022 result put into practice.
- `core/optimizer/StaticResumptions.scala` reduces a `shift` whose delimited
  context is syntactically known. It reuses the continuation in place when the
  shift is its last use and otherwise copies it as a join point; `Deadcode`
  then drops resets that nothing shifts to. This covers tail-resumptive and
  statically resolved handlers.
- `DirectStyle.scala` turns `val x = {…}; s` into a join point when the
  binding contains no non-tail call and no control operator.
- What remains goes to a first-order machine IR (`machine/Tree.scala`:
  `PushFrame`, `Return`, `Jump`, `Reset`, `Shift`, `Resume`). In LLVM it
  becomes `tailcc` functions that push **explicit frames onto Effekt's own
  stacks**. The C stack is used only for C foreign calls (`ccc`).
- Externs come in two kinds, `async` (they receive the stack) and plain
  synchronous ones. Effekt's host boundary is therefore opaque in exactly the
  sense the Codex review asks for.

So the LLVM backend is not selective CPS. It is static elimination plus
uniform explicit frames. The selectivity sits in the optimizer and in the type
system (capabilities say statically which handler a `shift` targets), not in a
per-function colour split. Other backends: JS (CPS, `TransformerCps.scala`,
with a direct-style mode for continuations it can contify), Chez Scheme
(monadic and call/cc variants), a core VM. MLton was dropped after 0.3.0.

## 2. Comparison with Koka and OCaml 5

**Koka: generalized evidence passing.** Xie & Leijen, *Generalized Evidence
Passing for Effect Handlers (or, Efficient Compilation of Effect Handlers to
C)*, ICFP 2021, PACMPL 5, Article 71, doi 10.1145/3473576 (verified).
Handlers are *dynamic* (nearest enclosing). An *evidence vector* (the handler
context) is passed as an implicit parameter, so `perform` indexes into it
instead of searching the stack. Tail-resumptive operations run in place as
direct calls. General resumptions use **yield bubbling**: the operation sets a
yield flag, every call site checks it and returns, building the continuation
on the heap as it unwinds, followed by a monadic translation to plain C. Koka
leans on row types and static evidence indices; Effekt leans on lexical
capabilities. Both obtain "the handler is known here" statically. Koka still
pays a per-call yield check in effectful code, while Effekt's LLVM backend
pays explicit frames everywhere and O(1) switching.

**OCaml 5: runtime fibers.** Sivaramakrishnan, Dolan, White, Kelly, Jaffer,
Madhavapeddy, *Retrofitting Effect Handlers onto OCaml*, PLDI 2021, doi
10.1145/3453483.3454039 (verified from the arXiv text, 2104.00250):
- Fibers are heap-allocated (`malloc`), growable stacks, and continuations
  are captured without copying frames.
- Continuations are **one-shot by design** (copying fibers is "unnecessary and
  inefficient").
- Handling an effect is "linear in the number of handlers", because handlers
  are dynamic and found by search.
- C calls run on a separate system stack.
- Mean overhead on code that uses no effects is 1%.
- No effect typing.

Of the three, this is the only design that needs no compiler knowledge of
where suspension can happen, and it buys that with a custom runtime stack,
which the JVM does not give us.

**Placement.**

| | Effekt | Koka | OCaml 5 | Klara v1 |
|---|---|---|---|---|
| Handler binding | lexical (capability) | dynamic + evidence | dynamic, searched | dynamic, deep |
| Who finds the handler | scope (static) | type-directed index | runtime search | runtime (v0: map merge) |
| Effect safety | static (captures) | static (rows) | none | runtime error |
| Multi-shot | yes (copy on shared resume) | yes | no | only when the capture footprint is empty (A-O6) |
| Capture mechanism | own segmented stacks (LLVM), CPS (JS) | yield bubbling | fibers | none yet (Codex §2) |
| Elimination when handler known | proven for λλCap (ICFP 2020, staged); optimizer passes in practice | tail-resumptive fast path | no | the proposal of §3 |

## 3. Mapping onto Klara

### 3.1 "Same result, different binding time": sound, with three conditions

Christian's claim: when the handler of an op is known at specialization time
(grade S, or A with a guard), `perform` compiles to a direct call and no CPS is
needed; otherwise fall back to selective CPS.

This is not only analogous to Effekt; one Effekt paper *is* this result with
types as the binding-time analysis. ICFP 2020 §1: "Statically knowing both the
handler for each effect operation and the stack shape, allows us to reduce all
abstractions related to effect handlers at compile time (Theorem 5.5)", and
the translation for λλCap "inserts staging annotations" (two-level λ-calculus,
Taha–Sheard terminology). The second-class restriction is exactly what makes
"handler known" a static fact. **Holds** as a statement about the literature.

For Klara it is sound under three conditions that types give Effekt for free:

1. **The specialization key is the handler context, not the op.** With dynamic
   handlers, which handler a `perform` reaches depends on the caller's
   extent. Effekt monomorphizes by stack shape; Klara must specialize a
   function per handler context it is entered under (Koka's evidence vector
   is the runtime form of that key). A closure that escapes and is called
   under another context needs another residual or a guard. That is A-grade,
   and the guard is on the handler-context identity/version.
2. **The guard must dominate every frame that a capture could need.** On the
   JVM you cannot turn live host frames into a continuation after the fact.
   A direct-style residual that discovers mid-run that it needed a real
   continuation cannot deoptimize into CPS. The guard is therefore checked at
   region entry, before frames exist, not at the `perform`. The only other
   deopt is **re-execution from region entry**, i.e. spindel's replay. That is
   legitimate only if the effect prefix since entry is replayable
   (deterministic ids S2, resume idempotence S6) or recorded. This is the
   real content of "erase dispatch", and it is a new obligation (G-O2).
3. **Erasure removes dispatch, not meaning.** Effect safety, which Effekt
   proves statically, remains a runtime check in Klara: performing an op with
   no handler is a runtime error. That is fine for an untyped core with
   optional narrowing, provided the narrowing layer can *certify* "no unknown
   handlers in this region" and so license dropping the fallback arm.
   (`algebras.md` §8 already names this the certified route.)

Under these conditions the S/A/D grade of the handler context selects the
tier. The construction is the dynamic counterpart of ICFP 2020 + Koka
evidence, and the Tübingen group has also built that dynamic counterpart: the
OOPSLA 2025 tracing-JIT paper shows that a meta-tracing JIT recovers much of
the elimination at run time. That is Christian's "runtime observation"
branch, and it already has a paper to compare against.

### 3.2 Recommended v2 JVM continuation strategy (refines Codex §2 and F §4.4)

One `perform`, four realizations, chosen per region by the grade of the
handler context and by the clause kind:

| Tier | Condition | Realization | Prior art |
|---|---|---|---|
| T0 | handler S (or A + entry guard), clause tail-resumptive or abortive | direct call / inlined clause / exception | Koka fast path; Effekt `StaticResumptions`; λλCap |
| T1 | handler S/A, one-shot, no host frames between `handle` and `perform` | selective CPS of exactly that region (partial-cps residual, explicit heap frames) | *Effect Handlers for the Masses* (type-selective CPS on JVM bytecode) |
| T1′ | one-shot, host frames in between (Klara → linked Clojure → Klara) | Loom virtual thread as the capture mechanism | F §4.4; X-F5 decides whether pinning kills it |
| T2 | handler D (unknown) | evidence-vector lookup, then T1/T1′ for the capture | Koka ICFP 2021 |
| M | multi-shot (`branch`, SMC, enumeration) | CPS residual over persistent state, or replay (spindel) | Effekt ICFP 2025 semantics: copy on shared resume, state per copy |

The host boundary stays opaque: a multi-shot capture across a linked host
frame is a named error, as Effekt's synchronous externs are.

### 3.3 Lexical vs dynamic handlers

**Recommendation: make handler instances lexical by default, keep dynamic
lookup as an explicit, named mode for ambient effects.**

- **Accidental handling.** With deep dynamic handlers, a library HOF that
  internally handles `:exn` (or `:choose`) intercepts the effects of the
  callback it was given. Zhang & Myers (*Abstraction-safe Effect Handlers via
  Tunneling*, POPL 2019) and Biernacki et al. (*Binders by Day, Labels by
  Night: Effect Instances via Lexically Scoped Handlers*, POPL 2020) show
  that lexical binding removes this by construction, and Effekt's contextual
  effect polymorphism is the user-facing form. Klara gets the semantics
  **without a type system**: `(handle [h Choose] body)` binds `h` as an
  ordinary lexical variable and `(perform h :flip)` targets that instance.
  Types (second-class, boxing) are needed only to rule out *escape*
  statically. Untyped Klara rules it out dynamically: when the `handle`
  exits, the instance is revoked, and a later `perform` on it is a runtime
  error, the same "consumed" state as spindel's settled `ForkHandle`.
- **Binding time.** This is the decisive argument for Christian's programme.
  With lexical instances, "which handler does this `perform` reach" is a
  *scoping* question: the handler is S wherever `h`'s binding site is inside
  the specialized region, and no per-context monomorphization is needed. With
  dynamic handlers it is a *calling-context* question and needs condition 1
  above. Lexical scoping makes dispatch erasure the common case rather than
  the speculative one. That is why Effekt compiles well.
- **What dynamic handling is still for.** Reference handlers (`H_world`,
  `H_host`, `H_meas`), virtual time, and spindel's interceptor lifting are
  *meant* to be intercepted by whoever installs a handler further out. Keep
  them as ambient effects with explicit dynamic `perform`. This is an
  ambient/lexical split, not a replacement.
- **Cost.** User code must name instances, or use sugar that binds the
  innermost instance at the `handle` site. Effekt shows this is livable.
  Whether it is livable for Clojure programmers is **Open** (G-O4).

### 3.4 Capabilities and authority

Effekt's capabilities are **scoped, not affine**:
- A capability can be used any number of times, but cannot outlive its
  handler (second-class), or its outliving is tracked (`at {caps}`).
- Spindel's authority is **affine**: settle exactly once, partition consumes
  the parent (S8, S9).

Klara needs both, and they compose:
- **A handler instance is a scoped capability.** Its lifetime is the dynamic
  extent of `handle`. Capture sets give Klara the footprint it already
  computes for copyability (`01-core-v1.md` §2: "Copyability of a closure is
  computed from its captures"). That rule *is* Effekt's capture set, computed
  at run time instead of typed.
- **A settlement or branch right is an affine token.** It may be held by a
  capability, but it is consumed by use.
- **Fork-resume** (Codex §2) is where the two meet. Resuming a continuation
  twice duplicates the capabilities it captured: scoped ones may be
  duplicated, affine ones must be split (σ, S9) or the resume is rejected.
  Effekt's ICFP 2025 runtime already has the matching state semantics: each
  copy of a multi-shot continuation gets its own stack-allocated state, which
  is the snapshot fork. Effekt has no notion of affine authority. Klara adds
  that, and it is a genuine research contribution rather than a re-derivation.
- *From Capabilities to Regions* links second-class capabilities to regions
  with subregion evidence. B's region tokens for transients are the same
  structure, which suggests one region discipline for both control and
  memory (**Conj**).

## 4. Our repos

### 4.1 partial-cps `feat/dual-mode-foundation` (read via `git show`; nothing checked out or modified)

Six commits, Jul 17–19 2026 (`d331687` … `ed9b382`). **None is on
`origin/main`** (v0.1.68): the branch is unmerged. The working tree in
`../partial-cps` is on this branch with uncommitted local changes, which I
left alone. What it does:

- `async+sync sync? body…` expands to `(if sync? <direct form> (async body…))`
  on both JVM and cljs. A literal `true`/`false` prunes the untaken arm at
  compile time (`ed9b382`).
- The direct form comes from `ioc/strip-breakpoints`. It resolves breakpoints
  with the same `var-name` machinery as the CPS transform, so whatever the
  async arm treats as a suspension point, the sync arm un-suspends. It is
  env-threaded through binders, emits site-free subtrees verbatim, and
  treats `fn*`/`reify*`/`deftype*` as opaque in both arms: a bare `await` in
  a fn literal is a compile error (`ca386be`).
- `invert` honours an `:interpretations` map (`:erase` → inline the
  argument): "the seam for runtime-steered multi-arm compilation (async*)".
- `async-expr?` marks async expressions. `all` gathers them, and all-warm
  inputs resolve synchronously.
- The law "sync ≡ async-all-warm" (value, effect order, exception class) is a
  seeded generative suite over 400 bodies (`equivalence_test.clj`).

**Relation to selective CPS.** partial-cps is selective CPS whose selection is
*syntactic*: a registered breakpoint symbol. The dual mode is a two-point
specialization of one body over a boolean handler context, i.e. T0 versus T1
of §3.2 chosen by a runtime flag. `:interpretations` is the beginning of
choosing by handler. Two limits:
- Closures are opaque, so `(map (fn [x] (await …)) xs)` is out of reach (F-D9).
  Effekt solves this case with contextual polymorphism plus a uniform
  stack, and Koka with effect-polymorphic compilation of HOFs.
- The selection is per breakpoint *name*, not per handler instance.

In Klara terms, `sync?` becomes the grade of the handler context, and
`strip-breakpoints` becomes the T0 residual of `specialize`.

**Correction to the brief.** konserve's ClojureScript portability does not come
from partial-cps. konserve has its own `async+sync` (`konserve/src/konserve/utils.cljc:112`),
a postwalk translation table over superv.async operators
(`*default-sync-translation*`), and no konserve branch depends on partial-cps.
F-D9 already records this. The partial-cps branch generalizes the konserve
pattern, and its first commit says it closes "the konserve/PSS
bare-symbol-strip hygiene hole". The real partial-cps consumers are datahike,
persistent-sorted-set and spindel (0.1.59–0.1.60 in their `deps.edn`). The
datahike store layer still uses *konserve's* `async+sync`.

### 4.2 The LLVM bridge

`grep -i llvm` over the `deps.edn`/README files in `~/Development`:

- **Ours:** `../metacarp` (`cyberwitchery/metacarp`, Christian's branch
  `carpaccio-library-abi`) and `../metacarp-upstream` (Veit Heller, release
  v0.0.3, 2026-10-25). Upstream has `carp-llvm-backend`. It lowers the same
  `BackendModule` the C backend renders, through the `carpentry-org/llvm`
  bindings (LLVM ≥ 21), has an LLVM JIT session for the REPL, and is at
  "reference-suite parity". Lowering covers closures with heap environments,
  sum types and ownership-planned deletes.
- `../carpaccio` embeds Meta-Carp as an affine DSL in Clojure and uses the
  **C** backend: it emits a rooted C module and loads it over Panama via the
  replikativ fork of coffi.
- **Not ours:** `tinywl-clj` (jjttjj; `org.bytedeco/llvm-platform` on the
  JVM), `cljrs` (MLIR/LLVM from Rust), `jank`, plus vendored LLVM, MLIR and
  Kotlin-native trees.

So the bridge is Carp → LLVM IR, not Clojure → LLVM IR.

**Effekt-style native path for Klara.** Three options, smallest first:
1. **Effect-free native tier (recommend now).** Only regions whose handler
   context is S and in which every `perform` reduced to T0 go to carpaccio.
   Residual control is a boundary error, mirroring Effekt's synchronous
   externs. Carp's ownership model fits this directly. No runtime work is
   needed.
2. **Port the Effekt runtime design into metacarp's LLVM backend.**
   - `rts.ll` is ~900 lines: segmented stacks, stable prompts,
     reference-counted continuations with copy on shared resume.
   - The structures map well onto Carp's affine discipline: rc=1 resume is a
     move, shared resume is a copy.
   - The cost is the machine-IR discipline: explicit frames, `tailcc`
     everywhere in effectful code.
   - Talking point: would Tübingen consider the runtime reusable as a
     library?
3. **Emit Effekt core and use Effekt's compiler.** This needs typed input, so
   it is viable only for a narrowed Klara fragment. It would make Effekt a
   backend rather than a peer. Not recommended except as a benchmark oracle.

### 4.3 pattern (pangloss/pattern; local branch `codex/recursive-dialect-sequence-abbr`, released as `org.replikativ/pattern`)

Rule combinators, nanopass-style `def-dialect`/`defpass`, an r3 rewriting
layer. It contains a toy Danvy-style CPS pass between dialects
(`test/cps/cps_test.clj`, self-described "early exercise") and Scheme→C and
compiler-course tests. It is the right tool for writing Klara's
core → specialized → CPS-residual passes as checked dialect transitions. Each
tier of §3.2 is a dialect, and "no `perform` survives into the native
dialect" is a dialect membership check, i.e. the boundary error of §4.2
option 1. It does not provide a continuation runtime.

## 5. Obligations and falsifiers

| Id | Claim | Status | Falsifier |
|---|---|---|---|
| G-O1 | T0 residual ≡ reference handler semantics whenever the guard holds (value, effect order, exception class): partial-cps's dual-mode law lifted to handler contexts | **Holds** for partial-cps's grammar (400 bodies); **Conj** for Klara | a generated body where the direct residual and the CPS/reference run differ |
| G-O2 | Every A-grade direct region checks its handler-context guard before any frame a capture could need; otherwise deopt = replay from entry with a replayable prefix | **Open** | a test where a closure escapes into another handler context and the direct residual reaches the wrong handler, or a replay that repeats a non-replayable effect |
| G-O3 | T0 `perform` costs ≤ 1.5× a plain `IFn` call on the JVM; T1 region allocation ≤ partial-cps today | **Conj** | JMH numbers on the Codex §2 benchmark |
| G-O4 | Lexical instances + ambient dynamic effects express all of `02-examples.md` and spindel interception, and remove accidental handling in the F-note HOF cases | **Conj** | an example that needs dynamic interception of a user (non-ambient) effect, or naming overhead users reject |
| G-O5 | Runtime capture footprint = Effekt capture set: a boxed Effekt value's `at {…}` and Klara's computed captures agree on a shared corpus | **Conj** | a program where the two classify a closure differently for a reason other than typing imprecision |
| G-O6 | Fork-resume duplicates scoped capabilities and splits affine ones; Effekt's per-copy stack state equals Klara's snapshot fork on state | **Conj** | a multi-shot program whose observable state differs between Effekt-LLVM and Klara M-tier |
| G-O7 | Klara-JVM on effect-handlers-bench is within 3× of Effekt-JS | **Open** | the numbers |

## 6. Talking points for Jonathan Brachthäuser

**What Klara takes from Effekt.**
1. *"Your ICFP 2020 staged translation is our design, with the binding-time
   analysis done by staging and runtime guards instead of second-class
   types."* Ask: did the λλCap restriction rule out programs you wanted? What
   does a *speculative* version (guard + fallback to λCap) cost to prove?
   Does "Back to Direct Style" give the correctness argument for our
   T1 → T0 erasure?
2. Lexical handler instances in an untyped language: escape becomes a dynamic
   revocation error. Ask whether they see a semantic trap in dynamic escape
   checking (Brachthäuser has written on scope-based vs type-based
   reasoning; OOPSLA 2022 is about exactly this).
3. The ICFP 2025 runtime as a native-tier design for an affine host (Carp).
   Ask about the non-reentrancy limitation in a setting with forks.

**What Klara offers in return (honest novelty).**
4. **Affine authority on top of scoped capabilities.** Effekt tracks where a
   capability may be *used*; spindel tracks that a settlement happens
   *exactly once* and that partitions are disjoint and exhaustive.
   Fork-resume with authority splitting is a problem their multi-shot work
   exposes and does not address.
5. **A JVM data point.** effect-handlers-bench (github.com/effect-handlers,
   last push 2025-08) has entries for Eff, Effekt, Hia, Koka, libhandler,
   libmpeff, libseff, Links and OCaml, and *no JVM system*. A Klara entry
   (T0/T1/Loom/CPS variants) would be new data on one-shot vs multi-shot
   costs on a host without stack access. It also revisits their own
   *Effect Handlers for the Masses* eight years on.
6. **Runtime-observed binding time vs the tracing-JIT paper.** Klara's grades
   with recorded reads and receipts are a structured, cacheable version of
   what a tracing JIT discovers. Proposal: a joint comparison on their
   bytecode corpus.

**Honest differences.**
- Klara is untyped at the core. Effect safety is a runtime check plus
  optional certification, and we will not match Effekt's static guarantees
  without the narrowing layer.
- Klara has interop with untransformed host code (linked Clojure frames)
  that no amount of compiler cleverness can capture through. Effekt controls
  its whole stack.
- Our multi-shot story leans on persistence and replay, not stack copying.

**Concrete asks.**
- (a) a pointer to the λλCap staged translation's mechanization, if any;
- (b) whether the LLVM runtime is meant to be reusable outside Effekt;
- (c) interest in a shared benchmark entry, or a student project on "lexical
  handlers in a dynamically typed, staged language", which fits the thesis
  topics on his page.

## Sources

Papers (PDFs read): schuster20capability, schuster22typed,
brachthaeuser22effects, mueller23continuation, muhcu2025multiple (all at
`pl.cs.uni-tuebingen.de/publications/<id>.pdf`); arXiv 2104.00250 (OCaml).
Abstract pages: brachthaeuser20effects, brachthaeuser2018masses, mueller23lift,
gaissert2025tracing. Effekt source: `effekt-lang/effekt@main`
(`core/optimizer/{Optimizer,StaticResumptions,DirectStyle}.scala`,
`machine/Tree.scala`, `generator/llvm/*`, `libraries/llvm/rts.ll`).
effekt-lang.org/evolution and /tour/captures. Koka: MSR page for the ICFP 2021
paper (abstract only; mechanism details from prior knowledge, **unverified**
beyond the abstract's "multi-prompt delimited control, generalized evidence
passing, yield bubbling, and finally a monadic translation"). *Effect Handlers
for the Masses* marking methods via Java's checked-exception mechanism:
recollection, **unverified**.
