# P. Klara and the ML family

Research note, 2026-10-28. Designer: Christian Weilbach. **Recommendation:** adopt ML's specification discipline, abstraction contracts and compiler analyses; adapt them to versioned bases and explicit authority. Do not make mandatory ML typing, whole-program closure, or heap images prerequisites for Klara's interactive semantics.

This extends A (calculus), G (Effekt), J (predictors), O (language graph), and `lambda-join/studies/ocaml.md`, rather than repeating their surveys. **Implemented**, **proved**, and **proposed** below are separate claims. Source inspection was performed; the external compilers and proof developments were not rebuilt.

Citation convention: `K:` means `/home/christian-weilbach/Development/klara/`; every other repository prefix means `/home/christian-weilbach/Development/<prefix>/`. Citations identify files and starting lines. Inspected HEADs: K `63551af`, ocaml `44c3e7d2e4`, ber-metaocaml `8891433d4`, eio `1fa7762`, wasm_of_ocaml `52f5ed29`, ocamljava `8330bfd`, real_world_ocaml `32ea926`, mlton `5fe9433`, polyml `4221cec`, cakeml `665f9b2`, hamlet `37275b9`. These are local snapshots, not claims about current upstream releases; the OCaml-Java and Real World OCaml checkouts are historical.

## 1. Specification culture: three different exemplars

The Definition of Standard ML separates static elaboration from dynamic evaluation, specifying core and modules with inference rules and explicit environments, stores and freshness conditions [1](https://people.mpi-sws.org/~rossberg/hamlet/). Its achievement is a reviewable language contract independent of an optimizing implementation. Its limitations are equally instructive: prose side conditions, mistakes and difficult metatheory remain possible despite mathematical notation.

HaMLet makes this concrete. `hamlet:eval/EvalModule.sml:73` labels executable cases with Definition rule numbers; rule 154 evaluates a functor body in its captured basis extended by the restricted argument. The file's opening comments record corrections to rule 182 and top-level declarations (`:12`). Static signature matching and fresh type names live separately in `hamlet:elab/ElabModule.sml:107`. Rossberg explicitly presents the interpreter as a faithful implementation modulo corrections, with independently selectable elaboration and evaluation [2](https://people.mpi-sws.org/~rossberg/hamlet/). This is executable specification discipline, not a verified compiler theorem.

**HaMLet is closer to T0 in role, but closer to the ansatz evaluator in structure.** T0 is Klara's practical reference execution path, a CEK machine with host extensions. The formal oracle is instead the compiled total `step` function, whose graph defines `Step` (`K:spec/README.md:3`, `:45`). Calling both “the reference interpreter” obscures which disagreements are bugs and which are fragment boundaries. Preserve both: name the formal evaluator “Core oracle,” and T0 “runtime reference.”

Harper–Stone supplies a complementary approach: elaborate surface SML into an explicitly typed internal language where modules, equality and coercions have precise meanings [3](https://people.mpi-sws.org/~dreyer/courses/modules/harper-stone-short.pdf). Lee–Crary–Harper mechanize an internal language's safety in Twelf, not an end-to-end proof of the entire surface Definition and its elaborator [4](https://www.cs.cmu.edu/~crary/papers/2006/tslf.pdf). A's distinction is correct. Klara should similarly assign separate obligations to reader, expander, typed elaborators and K0, rather than treating a K0 theorem as a theorem about all source programs.

CakeML verifies a significant SML subset in HOL4, including compilation and bootstrapping; it is neither a verification of every SML implementation nor exactly the full Definition (`cakeml:README.md:4`, `:44`). The 2014 verified REPL established permitted output behavior across parsing, checking, compilation and execution [5](https://cakeml.org/popl14.pdf). The modern `Eval` work supports dynamically compiled code sharing higher-order values with existing code [6](https://cakeml.org/pldi23-eval.pdf). Locally, `cakeml:compiler/repl/compiler64ReplProofScript.sml:1143` exposes explicit compiler, decoder, environment and typing premises. The lesson is to state the maintained session invariant, not merely prove each submitted expression in isolation.

For Klara, the next specification unit should therefore be a transition on **world root, pinned bases, pending definitions, authority store, executable cache and observable trace**. Begin with sequential definition/evaluation and cache installation; extend to forks and concurrency later. Specify failed publication, exceptions and recovery explicitly. CakeML does not supply Klara's adoption or authority theorem automatically.

Adopt a rule-to-code-to-test index, with a named counterexample for every erratum. Expand the corpus with generated scoped terms, shrinking and trace observations; distinguish divergence from fuel exhaustion. The existing spec-diff test excludes ambient operations and deliberately asserts that documented mismatches remain mismatches (`K:test-spec/klara/spec_diff_test.clj:218`, `:228`, `:242`). Passing it is valuable but is not full T0 equivalence. Track coverage and every exclusion alongside results.

Two corrections to older status statements matter: S5 already formalizes staging, and spec-diff exists (`K:spec/README.md:76`); `K:doc/architecture.md:431` still says otherwise. Progress is modulo named errors, and preservation is of scoping, not ML type safety. Authorities remain outside the formal fragment (`K:spec/README.md:91`). Record these corrections here without editing the older files.

## 2. Modules: interfaces are not worlds

ML modules solve several problems that Klara should keep distinct:

| ML mechanism | Klara counterpart or missing obligation |
|---|---|
| Structure and signature | Export bundle plus checked interface |
| Functor | Function from dependency bundles to export bundles |
| Sharing constraint | Explicit equality of abstract identities across imports |
| Opaque sealing / generativity | Hidden representation and fresh identity |
| Compilation environment | Basis selecting definition versions |
| Module language | Descriptor selecting elaboration and observation rules |

SML's functor applications freshen generated type names while preserving specified sharing (`hamlet:elab/ElabModule.sml:132`, `:393`). OCaml adds first-class module packages and applicative functor paths; strengthening records path-dependent equalities (`ocaml:typing/mtype.ml:42`). Unit-argument generative functors deliberately make distinct result identities on separate applications (`ocaml:manual/src/refman/extensions/generativefunctors.etex:28`). These are semantic abstraction choices, not merely namespace management.

Correct the earlier OCaml study's claim that this identity story comes “for free” from content addressing. Two applications of identical code to identical data can intentionally create incompatible abstract types. Their content hashes alone cannot encode freshness. Conversely, clients may need shared abstract identity across independently compiled modules. A runtime representation shared by two datatypes does not invalidate their static abstraction distinction; constructors also include extensible and exception cases with different identity mechanisms.

Worlds select versions and preserve old computations. Protocols provide operations; `defop`-style declarations can describe dispatch and effect obligations. Neither establishes representation independence or sharing. O's proposed descriptor specifies grammar, bindings, reference semantics and observations (`K:doc/background/research/O-racket-language-lattice.md:86`); using one descriptor per ordinary module would conflate language choice with dependency packaging.

**Propose signatures as immutable contract data**, referenced by export bundles and interpreted by the chosen language descriptor. Include exported names, shapes, abstract identity tokens, effect/authority obligations and optional law evidence. A module constructor is an ordinary function; an ML-like descriptor can check it statically, while dynamic clients receive wrappers and seals. Laws require proofs or checks: placing an equation in a signature does not make it true. Preserve O's directed language graph, without assuming arbitrary descriptors have a join.

Start with explicit generative seals and explicit sharing, leaving applicative identity as a later opt-in. Code identity must exclude accidental allocation identity; a module instance records both its construction recipe and any fresh seals. Define restoration rules before serializing seals. Real World OCaml's `Foldable.Extend` is a useful acceptance example: it derives operations while preserving `Arg.t`, rather than inventing a new collection identity (`real_world_ocaml:code/functors/foldable.ml:3`, `:18`; `extended_fqueue.ml:1`).

MLton supplies the staging analogy: known module arguments permit elimination of module abstraction and specialization of bodies, while runtime initialization effects retain their ordering. **Source correction:** today's pass called `Defunctorize` does not perform functor elimination; its documentation explicitly assigns that historical duty to elaboration (`mlton:doc/guide/src/Defunctorize.adoc:24`, `:73`). The actual application invokes `FunctorClosure.apply` and emits declarations (`mlton:mlton/elaborate/elaborate-modules.fun:175`). Klara can specialize module constructors under recorded dependency assumptions without confusing specialization with executing all initialization early.

## 3. Effects and concurrency: borrow the separation of mechanisms

OCaml 5 demonstrates that efficient handlers need not require a static effect-row discipline. Nevertheless, its effects are not simply “untyped”: `Effect.t` indexes the result type, and continuation input/output types are checked; what is absent is static assurance that every operation is handled (`ocaml:stdlib/effect.mli:25`, `:44`, `:70`). This qualifies the earlier study's “0% type system” wording.

One-shot continuation ownership is enforced at runtime: `ocaml:runtime/fiber.c:711` atomically takes the captured stack and rejects reuse. Fiber stacks make direct-style execution possible without transforming every call into heap-allocated CPS. The PLDI 2021 paper reports roughly 1% mean overhead on its non-handler macrobenchmarks [7](https://arxiv.org/abs/2104.00250); that is evidence for its implementation and workload, not a portable prediction for Klara/JVM. Native stack segments also need collector scanning, stack maps, unwinding and debugging support.

RFC 0002 deliberately differs in three ways: lexical instances for user operations, semantic tail/abort/general classes, and fork-resume under authority splitting (`K:rfc/0002-effects-and-handlers.md:23`). Retain those choices. Lexical targeting prevents unrelated handlers intercepting an operation; ambient host/world operations remain dynamically handled. Compile tail and abort cases directly, use CPS or explicit heap frames for general JVM effects, and investigate native segmented stacks separately. G already explains Effekt's more relevant lexical multi-shot design; OCaml's one-shot runtime is not a drop-in inference engine.

A copied stack is not a copied world. RFC 0001's data aliases are legal while consuming authority lives in a checked store. Current fork-resume splits randomness and borrows budget, but rejects captured resource and evidence authorities; it also does not itself defer irreversible effects (`K:rfc/0001-forks-and-authority.md:82`). RFC 0005 further restricts effects in owned islands (`K:rfc/0005-affine-regions.md:86`). These qualifications must accompany any “multi-shot supported” claim.

Do not revive the earlier promise that Lisp handlers can simply exceed OCaml across host callbacks. OCaml clears the parent stack across C callbacks (`ocaml:runtime/callback.c:46`); Klara also cannot capture intervening JVM frames (`K:doc/guide/03-effects.md:223`). An explicit replay protocol with logged inputs and effect restrictions is a separate implementation, not transparent capture. Likewise, falling back from entry is safe only before effects or in a replay-safe region; S7 frame-state deoptimization is a distinct path.

Separate scheduling from parallelism. OCaml domains map to OS threads, while fibers multiplex computations (`ocaml:manual/src/tutorials/parallelism.etex:26`). The multicore collector combines domain-local allocation with coordinated parallel minor collection and concurrent major work; barriers are visible in `ocaml:runtime/minor_gc.c:814`, and major-cycle accounting in `major_gc.c:56`. Klara should specify publication and authority-store synchronization using the JVM memory model first. It cannot inherit OCaml's memory-model guarantees merely by using immutable values.

Eio's most transferable contribution is structured resource lifetime: `Fiber.fork` associates children and errors with a switch (`eio:lib_eio/core/fiber.ml:11`), whose implementation tracks cancellation and release hooks (`eio:lib_eio/core/switch.ml:1`). Build direct-style I/O around scopes, cancellation, cleanup and explicit capabilities. Keep task spawn distinct from speculative world fork. Real socket I/O requires authority now; a deferred write intent cannot satisfy an immediate read dependency.

## 4. Staging: scope safety is only the first contract

BER MetaOCaml combines typed code construction with dynamic scope-extrusion checks. Klara already adopts quotation, escape and generated-name liveness; it does not yet provide MetaOCaml's typed generated-code guarantee. BER's implementation describes both extrusion and let-insertion, including controlled insertion loci (`ber-metaocaml:typing/trx.ml:62`, `:161`, `:259`). Its web documentation confirms typed code and imperative offshoring [8](https://okmij.org/ftp/ML/MetaOCaml.html).

Avoid calling staging wholly unformalized: S5 proves staged scoping invariants. What remains includes generated-name freshness needed for unrestricted binder-containing run/quote, explicit `lift`, `genlet`, recursive insertion and their runtime correspondence (`K:spec/README.md:100`, `:251`; `K:doc/semantics.md:358`). The current formal/T0 cross-stage persistence differences are enumerated in spec-diff, not resolved by the scoping theorem.

The highest-priority missing contract is **legal code motion**. Klara's `genlet` may hoist across functions and branches; the guide warns that evaluation can happen on unused paths (`K:doc/guide/05-staging.md:208`). “Pure” alone is insufficient: a pure division can fail, and a pure loop can diverge. Provide an explicit insertion locus and either prove that movement preserves termination, exceptions and effects, or document it as a generator-directed change in residual behavior. Scope correctness does not imply equivalence to naive splicing.

Typed staging belongs in the optional ML-like descriptor: code carries a result type, stage, free-name context and effect assumptions. Dynamic code crossing into it needs validation before execution. Type checking generation does not by itself certify native arithmetic, serialization, authority safety or arbitrary host constants. T0 permits some opaque cross-stage constants, whereas RFC 0004 rejects general closures and host objects without an explicit encoding projection (`K:doc/guide/05-staging.md:125`; `K:rfc/0004-canonical-edn.md:25`). Separate locally runnable code from portable code artifacts.

BER's offshoring converts an explicitly limited imperative subset to a low-level IR and rejects unsuitable expressions (`ber-metaocaml:ber-metaocaml-153/offshoring.ml:1`, `:44`). Adopt that boundary: first export a closed numeric kernel with specified overflow, layout, ownership and FFI contracts. Do not present a C printer as a semantics-preserving backend for arbitrary Klara.

## 5. Interactive persistence: save meaning before saving machinery

Poly/ML demonstrates that interactive compilation and persistent sessions coexist. Its compiler returns an executable thunk after elaboration and code generation (`polyml:mlsource/MLCompiler/COMPILER_BODY.ML:180`). Saved states can preserve incremental changes over parent images; loading restores existing mutable state but does not rewind every local or argument (`polyml:documentation/Reference/PolyMLSaveState.html:55`, `:69`). Code segments and processor-dependent relocations appear in `polyml:libpolyml/savestate.cpp:218`.

Isabelle builds substantial sessions on Poly/ML, managing ML heaps alongside session databases and documents [9](https://isabelle.in.tum.de/library/Doc/System/Sessions.html). This supports amortizing expensive library/proof initialization. It does not make a heap image a semantic world fork or an undo mechanism for external resources. Poly/ML's module persistence documentation explicitly ties loading to the same executable (`PolyMLSaveState.html:123`).

OCaml's toplevel maintains a value-binding table (`ocaml:toplevel/byte/topeval.ml:27`); successive source bindings can shadow old names without rewriting old closures. Utop improves the interactive interface, not the semantics into versioned world adoption. CakeML demonstrates that repeated dynamic loading can remain within a proof invariant. Klara adds explicit pins and world-relative resolution: ordinary closures capture their creation basis, while stored open definition closures use the resolving caller's basis (`K:doc/guide/02-world.md:174`). That distinction needs prominent REPL inspection tools.

For persistence, propose two layers. The **durable semantic manifest** contains canonical source/core values, descriptor versions, basis dependencies, contracts, receipts and reference semantics versions. A **host-specific compiled cache** contains executable artifacts, ABI/compiler versions, assumptions and certificate dependencies. Reload validates the second layer or drops it. RFC 0004's canonical encoding remains proposed, so portable content-addressed restoration is not already delivered.

Apply all R1–R8 to session restoration and editing (`K:doc/background/01-core-v2.md:221`): bounded publication work; acceptable first-result latency; cache deletion preserving traces; old/new basis coexistence; bounded cache cost; memory plateau under edits; shape continuity; and honest expansion dependencies. In particular, roots, seals, closures and executable loaders need reachability-based reclamation. Never serialize live resource authority as ordinary reusable data: restore via explicit reacquisition or reconciliation. Benchmark cold rebuild, warm cache reload and parent/child session loading separately.

## 6. Optimization: transfer facts, not a closed-world assumption

MLton's monomorphizer caches instances by vectors of concrete types (`mlton:mlton/xml/monomorphise.fun:42`). Its flow machinery propagates sets of lambdas (`mlton:mlton/closure-convert/abstract-value.fun:42`, `:87`); contification represents both return continuation and handler (`mlton:mlton/ssa/contify.fun:20`) and analyzes call graphs. Flambda's inspected pipeline repeatedly inlines, simplifies, removes closure variables and eliminates suitable references (`ocaml:middle_end/flambda/flambda_middle_end.ml:93`). This is Flambda in this checkout, not a claim about every Flambda 2 implementation.

The transfer boundary is precise:

| Analysis | Applicability to Klara |
|---|---|
| Constant propagation, reachability, known callees | Sound over an untyped IR with conservative unknowns |
| Closure/escape analysis and scalar replacement | Transfer if identity, failure order and capture behavior are preserved |
| Contification | Requires non-escaping continuations plus correct handler/authority scope |
| ML monomorphization | Direct for typed regions; shape specialization is the dynamic analogue |
| Unboxing and algebraic rewrites | Need representation and numeric evidence, including overflow |
| Whole-program dead code elimination | Requires a closed manifest excluding unknown entry points |

A lexical variable's binding can be stable while its callee performs general effects. Closure construction purity is not latent call purity. This reinforces J and G rather than introducing another analysis framework. In ordinary interactive mode, dependency-sensitive facts must be associated with the caller's basis; a new version cannot silently inherit an old proof. Current immutable roots and explicit pin changes support that separation (`K:src/klara/world.clj:125`, `:151`).

Collapse mode is MLton-like only when its manifest closes definitions, language rules, handlers and relevant host imports. A pinned world alone does not close reflection or external effects. In open mode, use guards, bounded specialization and generic fallback. The predictor ladder schedules profitable work; it does not turn profiling into proof (`K:doc/architecture.md:269`). RFC 0003's statistical replacement requires a separate approximation contract and must not weaken exact R3 invisibly (`K:rfc/0003-licensed-specialization.md:29`, `:60`).

Portability precedents sharpen this boundary. Wasm_of_ocaml lowers bytecode and its driver explicitly invokes flow analysis and an effects transformation (`wasm_of_ocaml:compiler/lib/driver.ml:100`); its local README records migration back into Js_of_ocaml. Historical OCaml-Java carries representation information into a dedicated JVM-oriented IR (`ocamljava:compiler/javacomp/javagen.ml:33`). These demonstrate backend engineering, not that OCaml 5's native stack runtime ports unchanged. Klara's KRI needs executable conformance tests for control, values and host boundaries.

## 7. Typing: make the ML experience a real opt-in

Hindley–Milner's principal type property applies to its defined inference calculus: a most general type summarizes all its instances. Full SML and OCaml add modules, mutation, value restrictions, overloading and extensions, so “every feature has annotation-free principal inference” is too broad. Still, mandatory checking provides a coherent default contract across a codebase, and abstract types prevent accidental representation dependence before execution. The earlier OCaml study undervalues that benefit when it reduces most typing value to linting.

Klara's plural predictors answer different questions: shape, latent effects, capture sets, ownership and cost. They need a common reference semantics and dependency discipline, not one universal principal summary. An inconclusive predictor may decline optimization; a declared typed language must reject a program outside its contract. These are different user promises, even if they share analysis machinery (`K:doc/background/research/J-type-systems-as-predictors.md:15`, `:26`).

**Yes: prototype an ML-style typed descriptor.** Start with rank-1 let polymorphism, closed algebraic datatypes, exhaustive matching, explicit module signatures and a conservative value restriction. Add effect/capture information before generalizing stateful or control-sensitive bindings. Typed staging can follow. Keep inference results outside CodeId, while recording the descriptor and elaboration semantics that determine what the source means.

Interop needs more than checking arguments once. Higher-order functions need wrappers checking calls and results; mutable references require mediated reads and writes or exclusion; abstract values require seals; polymorphic imports need a disciplined scheme, not one observed successful call. Unknown host effects cannot be certified pure. Ownership boundaries need stateful authority checks as RFC 0005 proposes (`K:rfc/0005-affine-regions.md:156`). A typed export depending on a redefined world binding must be revalidated for the new basis or retain its old pin.

Promise successful-result agreement with the untyped reference semantics, permitting additional rejection. Do not promise a gradual guarantee or parametricity until the boundary translation is proved. A restrictive descriptor is worthwhile even before it is a complete ML replacement: it offers reliable local inference, closed-world matching and checkable interfaces for kernels and libraries.

## 8. Positioning, priorities and tests of the argument

For researchers, Klara connects executable semantics, staged optimization and explicit authority to a versioned interactive world. SML contributes specification and module discipline; OCaml contributes production runtime experience. Klara's research claim is their integration with inspectable forks, not having invented effects, staging or interactive compilation. For practitioners, OCaml/SML remain stronger baselines for established typed libraries and predictable deployment. Klara's attraction is counterfactual execution and revisable computation under pinned meaning, with JVM/Clojure access today.

An ML programmer will miss pervasive inference, exhaustive datatype matching, enforced abstract interfaces, mature tools and broad optimized coverage. They may be surprised by named stuck states, caller-basis open definitions, runtime authority refusal and certificates that cover only particular transformations. These differences should appear in an onboarding example, including the current opaque host boundary and linked mutable state shared by forks.

Ranked adoption decisions:

1. **Adopt:** HaMLet-style rule indexing, errata examples and explicit spec-diff exclusions; highest benefit at lowest semantic cost.
2. **Adapt:** CakeML-style session invariants, initially for publication and cache installation, before claiming verified worlds.
3. **Adapt:** Eio-style task scopes, cancellation and resource cleanup, explicitly separated from speculative forks.
4. **Adopt:** checked module contracts and explicit abstract identities; protocols and worlds do not replace them.
5. **Adapt:** an ML-like descriptor with higher-order boundary contracts and a conservative typed fragment.
6. **Adopt:** flow/escape/contification analyses with basis dependencies; reserve unguarded whole-program assumptions for collapse.
7. **Adapt:** insertion loci, typed code evidence and a deliberately small offshoring IR.
8. **Adapt:** Poly/ML's layered session caching while retaining a portable semantic manifest.
9. **Avoid:** identifying hashes with generativity, one-shot stack copying with authority splitting, or tested caches with a verified implementation.

Two concrete collaboration experiments are justified. First, build a HaMLet-style rule/erratum corpus around Klara's oracle, then specify one CakeML-inspired REPL transition invariant and independently recheck the kernel fragment. Ask specification researchers to review the invariant and disagreement taxonomy, not endorse the whole runtime. Second, implement an Eio-inspired direct-style mock I/O scheduler on lexical effects, then one JVM adapter; port cancellation, nested-scope and cleanup tests, adding adoption/discard cases. Neither experiment requires porting an entire ML compiler.

The main claims have practical falsifiers:

| Claim | Experiment that could refute it |
|---|---|
| Contracts plus seals suffice before a full ML module calculus | Port `Foldable.Extend` and two generative abstract stores; a cross-store value accepted through checked APIs exposes inadequate identity enforcement |
| Oracle discipline improves confidence | Generate scoped staged/handler programs; an unexplained T0/oracle trace mismatch defeats claimed agreement for that fragment |
| Direct-style I/O composes with authority | Cancel during acquire, suspend and release; a leaked handle, double settlement or discarded write reaching the host refutes it |
| Compiler analyses transfer safely | Redefine an inlined callee across two pins; compare result, failure and effect traces with every cache removed |
| Persistence preserves meaning | Restore under a changed compiler/descriptor and erase compiled caches; changed observations or resurrected consumed authority refute it |
| Typed islands retain their guarantees | Send adversarial callbacks, mutable aliases and abstract values through dynamic clients; an unchecked typed failure refutes the boundary design |

Questions for Christian: Which first client justifies typed modules: inference kernels, reusable collection libraries, or the proof checker? Should abstract seals survive restoration as stable identities, and who may mint them? Is the first persistence promise portable replay or fast same-host restart? Should unsafe `genlet` motion require an explicit locus immediately? Which REPL transition should become the first theorem involving worlds and authority? Finally, should task spawn and speculative fork have distinct surface names from the outset?

## References

[1] Milner, Tofte, Harper and MacQueen. *The Definition of Standard ML (Revised)*, MIT Press, 1997. [Primary-language resources and errata](https://people.mpi-sws.org/~rossberg/hamlet/).

[2] Rossberg. [HaMLet: executable reference implementation and defects catalogue](https://people.mpi-sws.org/~rossberg/hamlet/). Local rule implementations cited above.

[3] Harper and Stone. [A Type-Theoretic Interpretation of Standard ML](https://people.mpi-sws.org/~dreyer/courses/modules/harper-stone-short.pdf), 2000.

[4] Lee, Crary and Harper. [Towards a Mechanized Metatheory of Standard ML](https://www.cs.cmu.edu/~crary/papers/2006/tslf.pdf), POPL 2007.

[5] Kumar, Myreen, Norrish and Owens. [CakeML: A Verified Implementation of ML](https://cakeml.org/popl14.pdf), POPL 2014.

[6] Sewell et al. [Cakes That Bake Cakes: Dynamic Computation in CakeML](https://cakeml.org/pldi23-eval.pdf), PLDI 2023, DOI 10.1145/3591266.

[7] Sivaramakrishnan et al. [Retrofitting Effect Handlers onto OCaml](https://arxiv.org/abs/2104.00250), PLDI 2021.

[8] Kiselyov. [BER MetaOCaml: implementation, typed staging, insertion and offshoring documentation](https://okmij.org/ftp/ML/MetaOCaml.html). Implementation details checked in the local N153 sources.

[9] Isabelle. [System manual: Theory Sessions](https://isabelle.in.tum.de/library/Doc/System/Sessions.html), session builds, ML heap images and dependencies.
