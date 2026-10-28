# K — Graal and Truffle on top of Klara: what staging must provide (research note, 2026-10-28)

Status markers as in B: **Holds**, **Conj**, **Open**. Paths are relative to
`Development/`; `klara/` paths are relative to this repository's root.

**Sources.**
- `graal` at `d2e7bd1e957` (2026-03-29, 25.1-dev), the checkout used by the
  earlier study `lambda-join/studies/graal-truffle.md` (cited below as
  *study*). This note builds on the study and does not repeat it. Thresholds,
  splitting numbers, the native-image blocklist, the interop value contract
  and the persistent-collection gap are all there.
- `graaljs` at `8d840b69657` (2025-11-01). `graalpython` at `3eceb5b2f` is
  **stale (2019)**, so I use it for one interop observation only.
  `truffle-play` is an Ethereum Truffle project, which is irrelevant here (the
  study made the same finding, study:4).
- Papers read from Zotero: Würthinger et al., "Self-optimizing AST
  interpreters", DLS 2012 (*DLS12*); "One VM to rule them all", Onward! 2013
  (*OneVM*); "Practical partial evaluation for high-performance dynamic
  language runtimes", PLDI 2017 (*PLDI17*, proceedings page numbers).
  Not in Zotero, marked *(recalled)* where I use them: Stadler et al.,
  "Partial escape analysis and scalar replacement for Java", CGO 2014;
  Flückiger et al., POPL 2018; Pettyjohn et al., "Continuations from
  generalized stack inspection", ICFP 2005.

## 1. Disagreements first

1. **"Interpreter plus `specialize` gives a compiler" (`doc/architecture.md`
   §4.1) only gives the front end.** In Truffle, partial evaluation (PE)
   produces a high-level graph. Most of the speed comes from what runs after
   it. With escape analysis disabled, Truffle languages run "an order of
   magnitude" slower. Without assumption folding they run 2–3× slower. Without
   PE they run more than 100× slower (PLDI17 p.671, Fig. 11). The authors also
   name the hard requirements on the backend: "deoptimization as a first-class
   primitive" with metadata, and assumption tracking (PLDI17 p.669 §5.3). In
   Klara, `specialize` has partial application as its reference meaning
   (`doc/semantics.md` §5), so it removes no overhead at all. The Futamura
   route therefore needs three things: a real specializer, a backend that does
   scalar replacement, and a deopt protocol. None of them exists yet.

2. **Klara should not copy Truffle's *online, automatic* PE. Its explicit
   staging is the better default.** Truffle's PE inlines everything unless it
   hits a `@TruffleBoundary`. The PLDI paper then concludes that "all code
   that was not explicitly designed for PE should be behind a PE boundary",
   after it saw "exploding code size or even non-terminating PE" (PLDI17
   p.668). BER-style staging inverts that default: everything is residualized
   unless it is escaped. Truffle finds binding-time mistakes late. A value
   that fails to become constant is a *compile-time bailout*
   (`graal/compiler/src/jdk.graal.compiler/src/jdk/graal/compiler/truffle/substitutions/TruffleGraphBuilderPlugins.java:1584-1597`),
   and PE-constancy is known to be fragile (study:67). In Klara a binding-time
   error is a stage error at generation time (`doc/guide/05-staging.md`
   :114-122). What Klara should take from Truffle is the *stage-polymorphic*
   interpreter, which `examples/staging/04-staged-interpreter.md` already
   has, plus the runtime protocol around it. It should not take the online
   PE algorithm.

3. **Klara's world guards are guards, not assumptions, and Truffle shows what
   that costs.** On every entry, `enter` checks every guard of every
   candidate executable (`klara/src/klara/stage.clj:159`), and that includes one
   `[:world sym value-id]` guard per free global (`stage.clj:89-94`). Truffle
   folds a valid assumption to nothing and records a dependency instead
   (`TruffleGraphBuilderPlugins.java:245-262`). Its measured gap is the 2–3×
   above. Research note C §3.2 already separates the two mechanisms, but the
   code does not. Klara can also do this *more cheaply* than Truffle. The
   world is an immutable root (`doc/architecture.md` §2), so whether a set of
   world reads is valid depends only on the basis root, and the result can
   be memoized by root identity. Truffle needs eager invalidation and
   per-assumption lists of dependent code because its heap is mutable
   (study:30).

4. **Entry-only deopt is more than a v1 simplification: it rules out most of
   Truffle's speculation.** `stage.clj:14-15` checks guards "on ENTRY (never
   later — live frames cannot be converted)". `klara.eval/deopt` may be
   returned only if no effect was performed (`klara/src/klara/eval.clj:59-62`,
   `:232-244`). Entry guards can speculate about arguments, captures and
   handlers, and nothing else. Truffle speculates per node on intermediate
   values (DLS12 §4; the `doLong` overflow rewrite at
   `graal/truffle/src/com.oracle.truffle.sl/src/com/oracle/truffle/sl/nodes/expression/SLAddNode.java:100-103`).
   S3 works with entry-only deopt for a narrow reason: the fused kernel
   performs no effect, so exact-or-throw lets it decline as a whole
   (`doc/background/impl/S3.md`:110-125). A T2 that specializes on the types of
   intermediate results needs deopt in the middle of a body.

5. **Note C says Klara cannot reconstruct frames without its own emitter
   (C §3.4(b)). That is too pessimistic.** T0's continuation is a list of
   plain-data frames (`eval.clj:8-12`). Residual code can therefore build a
   T0 machine state itself on a cold path and hand it to `drive`. Neither
   JVMCI nor HotSpot's deoptimizer is involved. Truffle gets frame
   reconstruction from the host VM because PE inlines the *interpreter's own
   methods*. Its deopt metadata is literally a stack of AST-interpreter frames
   (`ForNode.execute [bci: 39]`, with the frame as a virtual object; OneVM
   Fig. 15). Klara can produce the same metadata as staged code. The cost is
   cold-path code size and keeping live values alive. **Conj**; obligation K3.

6. **Content addressing makes profile conflation the default.** Truffle keeps
   profiles in mutable AST nodes, one per site (DLS12 §3). It needs splitting
   because sharing a call target conflates them (study:32). Klara terms are
   immutable maps, and CodeIds are α-canonical (`klara/src/klara/core.clj:41-42`,
   `:201`). Two textually equal lambdas in different places, or in different
   forks, have the same CodeId. The specialization cache is keyed by
   (CodeId, guard set) (`stage.clj:26`). So far Klara has no notion of a
   *site*, and it has no place where mutable profile state could live.

## 2. Mapping: Truffle's mechanisms and Klara's

| Truffle mechanism | Where (graal) | Klara today | Expressible through staging? |
|---|---|---|---|
| Self-specializing nodes: a finite lattice from uninitialized through specialized to generic; *correctness* (every state handles every input) and *finiteness* (no cycles) | DLS12 p.74; `Node.replace` calls `transferToInterpreterAndInvalidate` first (`truffle/src/com.oracle.truffle.api/src/com/oracle/truffle/api/nodes/Node.java:484-492`) | **Missing.** Terms are immutable and there is no per-site state | Partly. A generator can read a profile and emit the matching specialization. The lattice must live outside the term (R6) |
| `@CompilationFinal`: a field that is constant for PE and written only after a transfer | `PartialEvaluator.java:202-205`; PLDI17 p.665 | **Missing as a concept.** The closest analogue is a `[:captures]` or `[:statics]` guard | **Yes, if code values carry guards.** Read at generation time, `lift` the value, record the read as an assumption of the residual (R1) |
| Assumptions: fold `isValid` and record a dependency; install fails if the assumption was invalidated during compilation; invalidation deopts active frames | `TruffleGraphBuilderPlugins.java:245-262`; `TruffleCompilerImpl.java:866-878` | **Half.** `[:world …]` guards plus `invalidate!` (`stage.clj:164-177`) are lazy, are checked on every entry, and are not re-checked at install | Yes. Generation records world reads, and install re-validates them against the current root (R1, R2) |
| `transferToInterpreter` / `…AndInvalidate`: a `DeoptimizeNode` with action None or InvalidateReprofile | `TruffleGraphBuilderPlugins.java:382-394` | **Entry only:** the `deopt` sentinel (`eval.clj:59-62`) | **No form for it yet.** It needs a residual `deopt` node that carries a frame state (R3) |
| `@ExplodeLoop` (including `MERGE_EXPLODE` for bytecode loops) | `truffle/…/nodes/ExplodeLoop.java:59-90` | **Holds.** Unrolling is ordinary recursion at generation time (`examples/staging/01-power.md`, `02-matrix-vector.md`) | Yes, already |
| `@TruffleBoundary` | `PartialEvaluator.java:239` | **Holds, inverted.** Anything that is not escaped is residualized. Linked Clojure functions are host frames | Yes. This is the default |
| `isPartialEvaluationConstant`, `CompilerAsserts` | `CompilerDirectives.java:203`; bailout at `TruffleGraphBuilderPlugins.java:1597` | `code?` at generation time; stage errors | Yes, dynamically. A static check would need typed staging (05-staging:290) |
| `inInterpreter` / `inCompiledCode` | `CompilerDirectives.java:106,129` | Choosing the operations dictionary (`examples/staging/04-staged-interpreter.md`:45-73) | Yes. This is stage polymorphism (C, O10) |
| Frame virtualization; PE of the interpreter's own data | `FrameWithoutBoxing` (study:38); `PartialEscapePhase` after PE | **Holds for static structure.** The environment map and the dispatch disappear (04-staged-interpreter:90-92) | Yes, and better than PEA: interpreter structures are present-stage values. Guest allocations still need PEA (§4) |
| Deopt metadata: a tree of `FrameState`s (`outerFrameState` for inlining, `virtualObjectMappings` for escape-analyzed objects) | `compiler/…/nodes/FrameState.java:169,178`; `PartialEscapeClosure.java:459-479`; PLDI17 p.669 §5.2 | **Missing** | Yes, if the generator can reify its own T0 state as code (R3, R4) |
| Speculation log: failed speculations are not tried again | `OptimizedCallTarget.java:331,1136`; `PartialEvaluator.java:625-628` | Design only ("poisoned against the guard that lied", C §4.3.6) | Not a staging feature. It is evidence read by the generator (R7) |
| OSR: `BytecodeOSRNode`, threshold 100,352 back edges | `truffle/…/nodes/BytecodeOSRNode.java:62-131`; `OptimizedRuntimeOptions.java:239` | **Nearly free.** `recur` expands to `app` (`klara/src/klara/expand.clj:412-413`). Every `app` goes through `call-value*` and so through the entry hook (`eval.clj:246-251`, `:299`) | Yes. A loop iteration is a closure entry |
| Frame introspection through deopt metadata (Python `sys._getframe`) | OneVM §6 | Not applicable: no compiled code exists | It becomes the mechanism for **fork and capture** out of compiled code (R5) |

Summary. Klara already has the generation-side half of Truffle: unrolling,
boundaries, stage polymorphism, and the removal of interpreter data
structures. It lacks the whole runtime half: assumptions folded into
residuals, deopt points inside a body, frame states, profiles and the
speculation log. All of the missing parts except profile storage can be
written as *staged code*, provided code values gain guards and deopt nodes.

## 3. Can T0-in-Klara plus `specialize` yield a compiler the Truffle way?

Yes, for the first projection, under a binding-time discipline that I state
here. Klara has no metacircular T0 today. `klara.eval` is a CEK machine in
Clojure, and `doc/architecture.md` §3 allows either a Klara T0 or a host seed.

**Binding times of a CEK interpreter written in Klara.**

| Static (generation time) | Assumed (static under a guard, like `@CompilationFinal`) | Dynamic |
|---|---|---|
| the K0 term and its CodeId, op tags, de Bruijn indices, arity, the *shape* (length) of the locals vector, the clause key sets of `handle`, prim names, the static prefix of the continuation | world values reached by `resolve`, profile state per site, absence of dynamic handlers (`[:unhandled]`, `stage.clj:23-24`), op class of a perform site | local values, arguments, results of host calls, the continuation beyond the static prefix |

Rules:

1. **The driver loop must unfold only while control is static.** `drive`
   (`eval.clj:655-668`) loops over machine states. Truffle uses
   `MERGE_EXPLODE` for the same purpose in bytecode interpreters
   (`ExplodeLoop.java:73`). In Klara this is generation-time recursion over the
   term. It stops at points where the continuation depth becomes dynamic,
   meaning non-tail calls to unknown closures.
2. **Specialization points are memoized by `with-genletrec`.** The key is
   (CodeId, static environment shape, assumed values). This is offline PE's
   polyvariant specialization point (Jones–Gomard–Sestoft), and Klara already
   has the mechanism (05-staging:242-273). It also gives termination for
   recursion (the Ackermann example).
3. **Congruence.** A value computed from a dynamic value is dynamic.
   `lift` turns a present value into code. A residual must never depend on a
   generation-time read that is not recorded. Note C's O4 (read-set
   completeness) applies to generators unchanged.
4. **The continuation is partially static.** Frames pushed by static code
   are generation-time data. This is what makes frame states cheap (R3): the
   generator *knows* the T0 continuation prefix at every residual point.
5. **Effects are residualized by op class** (RFC 0002). A tail-resumptive op
   becomes a direct call. An abortive op becomes a host exception. A general
   op either needs a selective-CPS region or capture by deopt (Q4).

**Where Truffle needed compiler intrinsics, and the Klara counterpart.**

| Truffle intrinsic | Why the compiler had to know about it | Klara counterpart |
|---|---|---|
| `transferToInterpreter` → `DeoptimizeNode` | a control sink with no successors; the code it dominates is dead (PLDI17 p.668) | residual `(deopt state)`. **Must be added** to code values and to every backend |
| `Assumption.isValid` folding and recording | zero-cost check, dependency registered at install | an assumption set in code-value metadata, validated at install and per basis root (R1, R2) |
| `@CompilationFinal`, `@Child` | PE reads through fields of the constant receiver | not needed: interpreter data is present-stage. Klara needs only `lift` plus a recorded assumption |
| `isPartialEvaluationConstant` | bailout when binding time is wrong | `code?` at generation time, or later a typed narrowing layer |
| `injectBranchProbability` | block layout | a hint annotation in code; trivial |
| `ensureVirtualized`, `materialize` (`CompilerDirectives.java:512,550`) | control over PEA | needed only for guest allocations (§4) |
| `profiledPERoot`, found by name (study:13) | where PE starts | the generator's entry; ordinary Klara |

The certification angle is where Klara can do better than Truffle, which
has no certificates. With a stage-polymorphic interpreter, the obligation
"residual ≡ interpretation" reduces to two parts: per-operation agreement of
the interpreting and generating dictionaries (O10), and soundness of staging
itself. Staging soundness is not proved, and one hole is already known:
`genlet` floats impure expressions past conditionals
(`doc/background/impl/S4.md`:127-128).

## 4. Graal techniques that T2 needs: a minimal set

Truffle's minimal list from PLDI17 p.669 is short. The backend must
(a) support deopt as a first-class primitive with metadata, (b) track
assumptions, and (c) do escape analysis, "the most important optimization".
For PE output, the backend's own inlining is "not important at all". For
Klara this gives the following list.

**Required for a credible T2:**

1. **Assumptions folded per basis root** (R2): the 2–3× item.
2. **Speculative guards inside the body with deopt to T0** (R3): types of
   intermediate values, unboxed longs and doubles with exact-or-throw
   arithmetic. S3's overflow discipline and `SLAddNode.doLong`'s
   `rewriteOn = ArithmeticException` are the same pattern. Klara needs it at
   every operation, and so far has it only at entry.
3. **Inlining as s-m-n with a budget measured after specialization.**
   Truffle decides inlining on node counts after PE (study:33). Klara already
   has `code-size` (05-staging:31-34). The generator emits the specialized
   callee, measures it, and keeps it or residualizes a call.
4. **Scalar replacement of guest allocations.** This is required on hosts
   without escape analysis. On the JVM, C2's (non-partial) escape analysis
   covers some cases if T2 emits bytecode. Chez does no Graal-style partial
   escape analysis as far as I know (**Open**). PEA's coupling to deopt is
   the essential point: "Deoptimization instructions are not escape points.
   Instead, information about the virtual state of an object is stored in the
   scope descriptor" (PLDI17 p.669; `PartialEscapeClosure.java:459-479`).
   Klara values are immutable, and identity is observable only through
   `:host/call` (`identical?` is not a Tier L prim,
   `klara/src/klara/core.clj:61-69`). Klara can therefore rematerialize a virtual
   value at a deopt point, or even duplicate it, without the identity
   bookkeeping Stadler et al. need *(recalled)*. Every `:host/call` in a
   region is an escape point.
5. **Deopt-cycle budget** (15 cycles, 100 compiles; study:31) together with
   DLS12's finiteness rule.

**Not needed yet:** a sea-of-nodes IR, global code motion, register
allocation and Graal's own inliner. The host compiler (C2 for bytecode, Chez)
does that work. **OSR** comes almost free at T0, because loops are self
tail calls through the entry hook (§2). OSR *out of* T2 into T0 is ordinary
deopt.

## 5. Polyglot interop: lessons for hosting Clojure and other languages

1. **The protocol must have cached and uncached forms, both generated from
   one definition.** `InteropLibrary` is generated from `@GenerateLibrary`
   with default exports for the boxed primitives
   (`truffle/src/com.oracle.truffle.api.interop/…/InteropLibrary.java:186-198`).
   It has an uncached slow path (`:3159`), and use sites cache per receiver
   class with a `limit`. In Klara, host access is the ambient effect
   `:host/call` (`doc/semantics.md` §7). That is more general, because a handler
   can reinterpret it. A T2 must specialize a `:host/call` site to a resolved
   method under an `[:unhandled #{:host/call}]` guard, and S3 already does
   exactly this for its region.
2. **Classify foreign values by trait.** GraalJS gives a foreign object a JS
   prototype according to the messages it answers: array, instant, hash,
   iterator, string, number, executable
   (`graaljs/graal-js/src/com.oracle.truffle.js/src/com/oracle/truffle/js/nodes/interop/ForeignObjectPrototypeNode.java:63-90`).
   For Klara hosting Python or JS, the trait set must include **persistence
   and functional update**, which `InteropLibrary` lacks (study:23,41).
3. **Mutable guest heaps conflict with forks.** GraalJS forbids concurrent
   access to JS objects (`graaljs/docs/user/Multithreading.md:18`).
   Klara's equivalent hazard is already visible in "L0 linked" state, which is
   "shared by all forks" (`doc/guide/07-clojure-interop.md:58`). A hosted
   language with mutable objects needs its heap as an RFC 0001 authority
   (copy-on-fork or split), or it is not forkable.
4. **Boundaries must be explicit and checkable.** Truffle warns when an
   indirect call survives PE (PLDI17 p.668). Klara's rule is that only the 44
   Tier L prims have specializable meaning and every other Clojure function
   is a host frame. That is the right default. Specializers should *report*
   residual host calls in receipts.
5. **Avoid two value worlds.** Klara's phase 0 shares Clojure's
   collections. That is exactly what Truffle cannot do (study:41, 85).

## 6. Native Image's closed world and Klara's collapse

| | Native Image | Klara collapse |
|---|---|---|
| what is closed | code reachable by points-to analysis from `main` and the image heap roots (`graal/docs/reference-manual/native-image/NativeImageBasics.md:185-193`) | world cells listed in a manifest. The expander *records* reads, so the reachable set is exact, not an over-approximation |
| reflection, dynamic lookup | needs metadata at build time (`Compatibility.md:27-39`) | `:world/resolve sym`, `eval` and `:host/*` must be in the manifest |
| build-time initialization | a heap snapshot, with semantic hazards (`ClassInitialization.md:17-41`) | the world *is* a snapshot (an immutable root). Hazards remain only for linked host state |
| runtime eval | Truffle-on-SVM bakes three copies of each PE-reachable method (study:15) | keep T0, the expander and the code-value machinery. On Chez, runtime compilation stays available |
| when the closed world is violated | build failure (blocklist) or a missing-registration error | **must be decided (Q6):** a hard error, or fallback to T0 |
| profiles | PGO from an instrumented run | receipts, predictor level 3 |

The structural difference is that Native Image *infers* the closed world
and Klara *declares* it, checked against recorded reads. Collapse is then
specialization with every manifest cell as an assumption whose failure has
no generic path. That makes O9 (collapse adequacy) the guarded-specialization
square with the fallback arm removed.

## 7. What Klara's staging mechanism must add

- **R1. Assumptions in code values.** Each code value carries the set of
  world and profile reads its generation made (`(code-assumptions c)`).
  Install re-validates them against the current root and rejects with a
  retryable reason, as in `TruffleCompilerImpl.java:866-878`. The
  certificate's `:assumptions` field (`stage.clj:118`) then becomes
  *computed*, not hand-declared.
- **R2. Guards and assumptions as first-class values.** The guard vocabulary
  is a closed set of tuples (`stage.clj:17-24`) with a closed predicate map
  (`stage.clj:58-61`). Required: user-definable guard values, union as the
  join (C §4.1), and assumption validity memoized per basis root, plus a
  re-check at loop headers for long-running fibers that raise their basis.
- **R3. A residual `deopt` form carrying a frame state.** A frame state is
  code that builds a T0 machine state `[:eval term env kont]` from residual
  locals: the term by CodeId and path, the static environment shape filled
  with residual variables, and the static continuation prefix as data. It
  nests through inlining, like `outerFrameState`. The generator needs a
  `reflect-state` operation that turns its present T0 state into such code.
- **R4. Virtual-object descriptors.** Code in the frame state that rebuilds
  a value whose allocation was elided. It is sound to duplicate under the
  identity rule of §4.
- **R5. Reification by unwinding at residual call sites.** Each residual
  call site has a frame state. A capture signal (a general effect, a fork, an
  inspection, or deopt of a caller) unwinds, and each frame appends its T0
  frame, as in generalized stack inspection (Pettyjohn et al. *(recalled)*).
  This is PLDI17's lazy deoptimization (p.669) done without VM support. The
  same metadata then serves four purposes: deopt, capture of a general op,
  fork, and debugging.
- **R6. Site identity and profiles.** A site is (CodeId, path), optionally
  qualified by fork. Profiles are monotone states in a finite lattice
  (DLS12). A generator's read of a profile is a recorded read, and
  regeneration happens only on a lattice transition.
- **R7. A speculation log** per (CodeId, site, guard), with the 15/100
  budget.
- **R8. A `run` that compiles and installs.** Today `run` interprets and
  never reaches the cache (05-staging:299-302; S4.md:134-135). Code value
  → executable → certificate is the missing connection.
- **R9. A linear `reify` distinct from `lift`.** `lift` rightly refuses
  continuations and handler instances (05-staging:145-158;
  `eval.clj:428-452`). Frame states *move* a continuation rather than copy
  it, so they need a one-shot form that is consistent with RFC 0001.
- **R10. Op class on residual perform sites** (RFC 0002), so that T2 can
  choose between a direct call and reification.
- **R11. Formal rules.** A two-level `Tm` with `assume` and `deopt`, in the
  style of Flückiger et al. *(recalled)*, with frame-state correspondence as
  a bisimulation.

## 8. Obligations and falsifiers

| # | Claim | Status | Falsifier |
|---|---|---|---|
| K1 | A stage-polymorphic Klara T0 specialized to a program removes all interpretive dispatch (no op-tag tests, no env lookups in the residual) | **Conj** (holds for the tiny Lisp, 04-staged-interpreter:90) | a residual for a K0 program with `handle` or `letrec` that still dispatches on `:op` |
| K2 | Per-root memoized assumption checks bring entry cost to O(1) when the world is unchanged | **Conj** | entry cost growing with the number of free globals on an unchanged root |
| K3 | Deopt in the middle of a body via a frame state is observationally equal to the generic run: effects already performed are not repeated, and the rest agrees | **Open** | force every guard to fail in turn on a corpus and compare effect traces with T0. Any repeated or missing effect falsifies it |
| K4 | Rematerializing elided values at deopt is sound because identity is observable only through `:host/call` | **Conj** | a Klara program that distinguishes two rematerialized copies without a host call |
| K5 | Capture by deopt costs nothing on paths that do not capture | **Conj** | on the JVM, a measurable slowdown of non-capturing T2 code from exception handlers, against the 2.7× CPS tax (`doc/architecture.md` §3) |
| K6 | Capture by deopt is acceptable only for rare general ops | **Conj** | an SMC workload where `choose` fires every step and capture by deopt loses to selective CPS. Expected; this decides Q4 |
| K7 | The profile lattice is finite, so regeneration terminates (DLS12 finiteness) | **Conj** | a workload that cycles through regeneration within the 15/100 budget |
| K8 | Collapse = specialization with failure-free manifest assumptions satisfies O9 | **Open** | a collapsed artifact that diverges on a run respecting the manifest |
| K9 | Residual ≡ interpretation reduces to per-operation agreement of the two dictionaries plus staging soundness | **Conj**; staging soundness has a known hole (genlet purity) | a residual that disagrees although the operations agree pointwise |

## 9. Questions for Christian

1. **Futamura route or direct compiler first?** `doc/architecture.md` §4.1 says
   direct first. Does a metacircular, stage-polymorphic T0 in Klara become a
   goal in its own right, given that it is also the only route that makes
   K9 certification possible?
2. **Mid-body deopt.** Do you accept changing the guarded-specialization
   square from "replay from entry" to "resume at the reified state" (K3)?
   It is the precondition for any type speculation.
3. **Where do profiles live with respect to forks?** If they are shared, a
   fork is warm, but its performance (and its receipts) depend on sibling
   forks. If they are per fork, every fork starts cold. Should they be
   evidence under the held-out discipline?
4. **Capture by deopt or selective CPS** for general ops, decided per op by
   predicted capture frequency?
5. **A linear `reify` beside `lift`** for frame states. Is that acceptable
   under RFC 0001, or should frame states be confined to the runtime and never
   be Klara values?
6. **Collapse:** when the manifest is violated, hard error or fallback to an
   embedded T0?
7. **Should the KRI require identity-free persistent values,** so that K4
   holds by contract on every host?
