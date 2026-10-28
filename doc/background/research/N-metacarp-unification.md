# N — Klara and metacarp as one system

Research assessment, 2026-10-28. Recommendation: unify around a checked native-region contract, then a K2-to-metacarp translation. Keep Klara's world and effect semantics and Carp's static native semantics as two regimes of one system. A common source language or universal runtime is neither necessary nor presently justified.

## 1. What Klara should learn, and corrections to H

### Evidence and scope

Paths below are relative to `/home/christian-weilbach/Development/`. **K** means Klara at `b666caf`; **U** means `metacarp`'s `origin/main`, `512ef81`; **I** means its checked-out integration branch `carpaccio-library-abi`, `c275e44`; **R** means `research/memory-region-facts`, `5e5130d`; **M** means `memory-effect-manifests`, `69ea2b6`; **C** means carpaccio's checked-out `upstream-metacarp`, `2a91410`. Branch-qualified citations refer to `git show REF:path`, not necessarily the working file. Proposals below are inferences, not implemented features.

I inventoried all local and remote branches and compared their divergent changes with U, grouping duplicate and merged refs. Relevant additional tips are `upstream-ownership-data` (`2d36094`), `upstream-ownership-summaries` (`f787567`), `upstream-foreign-contract-data` (`609b878`), `upstream-c-layout-assurance` (`9d0056e`), `session-emit-library` (`b025b47`), `session-ownership-core` (`bec72ec`), and `origin/ct-set-theoretic` (`860cee1`). Backup/review/rooted-emission branches overlap these changes; `carp-nrepl-extract` is a separate, no-common-ancestor transport extraction. I also inspected recent upstream fixes and carpaccio's divergent `main` (`d36763d`). No branches were checked out or fetched. Findings establish source-level evidence, not a fresh execution of the compiler assurance suites.

**Klara already names the unification seam.** K1–K3 do not exist; Chez is the planned native baseline, metacarp the kernel route, and the backend receives closed code while Klara retains world-dependent decisions (`klara/doc/architecture.md:10–15,63–78`, K). H's categorical rejection of IR sharing and requirement to go through surface forms are therefore too restrictive (`klara/doc/background/research/H-metacarp-veit.md:351–359,386–388`).

### Corrections that change the design

**Captures copy; they do not move.** H says capturing an owned value moves it. U explicitly excludes lambda capture from consumption and explains that two closures can capture one original; backend construction deep-copies managed captures (`metacarp/carp-ownership/carp-ownership.carp:794–799`; `metacarp/carp-backend/carp-backend.carp:163–167,948–973`, U). Calling a closure borrows its callable value, and consuming a capture inside its reusable body is rejected (`metacarp/carp-ownership/carp-ownership.carp:765–769,1716–1744`, U). These are distinct rules. Copying an array is legitimate Carp semantics; copying a Klara evidence authority is not. Reuse the consumption analysis, never the capture policy wholesale. Nor does affine ownership mean that Carp functions are intrinsically one-shot: ordinary closure invocation is repeatable.

**carp-ir is not monomorphized backend IR.** It contains resolved identities, lambdas, calls, annotations and type variables; it deliberately excludes dependencies on the reader and type implementation. Concrete types arrive in `SpecializedExpr` later (`metacarp/carp-ir/carp-ir.carp:6–26,41–64`, U; `metacarp/carp-specialize/carp-specialize.carp:24–65`, U). H conflates these stages. Klara can translate to either stage, with different obligations.

**Keep three levels of memory work separate.** M's manifest carries direct effects, invalidation indices and an evidence string; U retains direct manifests but explicitly says emitted C is not checked against them (`metacarp/carp-ir/carp-ir.carp:102–124`, M and U). R computes a bounded monotone propagation of four booleans over specialized calls, retaining direct sites and unresolved leaves. It does not implement the full argument-remapping, Store-sensitive SCC analysis proposed in #74 (`metacarp/carp-memory/carp-memory.carp:561–632`, R). Its verification result is explicitly relative to declared native contracts (`metacarp/carp-memory/carp-memory.carp:786–789`, R). A field named `Proven` or `checked` is not a Klara kernel certificate.

**The analogies in H are useful but not equations.** `noalloc` excludes allocation/resize and unresolved effects; it does not bound existing retained bytes, stack growth, deadlines, or the enclosing runtime's allocations (`metacarp/carp-memory/carp-memory.carp:636–648,729–784`, R). Arena non-escape prevents dangling storage; snapshot isolation requires versioned visibility and forbids observing subsequent parent changes. A perfectly live outside object can still violate isolation. Likewise, freezing requires immutability and lifetime independence; carpaccio's `snapshot` is a field-by-field persistent-map copy, not an ownership transfer (`carpaccio/src/carpaccio/shared.clj:354–358`, C).

**Do not turn limitations of summaries into limitations of inference.** H's “lifetimes … not quantified” applies to exported concrete `borrows-from` summaries. U's inference preserves named quantified lifetimes through generalization and instantiation, while keeping local value lifetimes un-generalized (`metacarp/carp-infer/README.md:13–19`, U). Structured places also do not imply comprehensive enforcement: U calls them preparation for later checking; I documents whole-root strict foreign calls and relaxed intrinsic mutation (`metacarp/carp-ownership/README.md:48–64`, U; `metacarp/docs/semantic-delta.md:148–161`, I).

H additionally overstates that imprecision must *never* reject code. Klara explicitly permits opt-in narrowing annotations to reject programs (`klara/README.md:91–96`, K). Automatic optimization should fall back when unproved; an explicit “check this affine region” request may report failure. These interfaces should be distinguished.

### Lessons beyond H

Adopt metacarp's **separation of decisions from placement**, but recognize it remains an objective: #74 identifies multiple current owners of heap events. There is now a narrower cross-backend memory-fixture gate; H's historical account should not imply no emitted-program checking exists at all (`metacarp/scripts/check-llvm-memory.sh:2–7,33–57`, U). Coverage of selected fixtures is still short of a universal leak gate.

Adopt **generation lifetime as part of correctness**. U's ordinary JIT edits invalidate published native code; its narrow Float-function API instead returns immutable generations with host-owned publication policy (`metacarp/carp-session/README.md:19–31`, U). Carpaccio retains old libraries until explicit close (`carpaccio/docs/architecture.md:9–21`, C). Klara's pinned bases require the latter discipline for every reachable executable, callback and deleter. A shared resident compiler session is not itself a forkable world.

The integration branches already suggest a useful shared protocol. `OwnershipFunctionSummary` separates parameter modes from result ownership and retained input borrows (`metacarp/carp-ownership/carp-ownership.carp:69–109`, `upstream-ownership-summaries`). Carpaccio `main` actually consumes those summaries and refuses missing or arity-inconsistent manifests; C instead conservatively assigns unique loans (`carpaccio/src/carpaccio/runtime.clj:139–172`, `main`; `carpaccio/src/carpaccio/runtime.clj:86–90`, C). This is a demonstrated second consumer on a divergent branch, not an upstream-wide capability. Preserve that separation of ownership, exclusivity and lifetime in Klara's interface.

## 2. Six routes to unification

### (a) Carp ownership as the static affine narrowing layer

**Feasibility: high for closed native regions; medium for a reusable analysis; low for immediate whole-language reuse.** The existing pass runs after concrete specialization, classifies owned types through `delete`, threads move/origin state, and returns a side-table plan (`metacarp/carp-ownership/README.md:3–36`, U). Klara authorities instead are aliasable IDs whose lifecycle resides in a store, with lazy branch resolution (`klara/rfc/0001-forks-and-authority.md:24–39,82–90`, K).

Define a separate authority analysis domain sharing place, move, borrow, context and witness vocabulary. Lower an established resource transfer to an affine native token; represent copyable Klara data as borrowed inputs or runtime-managed handles. Give split/join/settle explicit operations. At a world lookup, unknown callback or unresolved alias, keep dynamic authority resolution. Never classify authority as duplicable merely because its ID is an unmanaged integer. Never attach an ordinary data copier to it.

Erasure should mean removing redundant validation within a proved region. Splitting randomness, debiting budget and changing settlement state remain semantic actions. Local single-use analysis does not prove evidence conservation, exhaustive partition, concurrent exclusion, or fail-closed durable settlement (AU2–AU7, `klara/rfc/0001-forks-and-authority.md:72–78`, K). An entry guard must establish all external alias/lease assumptions; checks at uncontrolled boundaries remain.

**Cost:** medium to high: parameterize analysis, add fork-sensitive rules, and establish simulation against T0 traces. **Gains:** Klara obtains concrete checking and diagnostics; metacarp obtains another consumer and stronger regression cases. **Concessions:** Klara accepts conservative region rejection or generic fallback; metacarp must separate reusable analysis concepts from Carp-specific destruction. Requiring Carp itself to acquire Klara authority semantics would greatly increase the cost.

### (b) metacarp as a K3 backend alongside Chez

**Feasibility: high for typed kernels, much lower for the entire KRI.** Both C and LLVM consume the same lowered `BackendModule`, sharing specialization, ownership and lambda lifting (`metacarp/carp-llvm-backend/README.md:3–8`, U). Use that infrastructure, first through validated Carp input or resolved IR; do not manufacture backend modules that silently bypass ownership planning.

Start with scalar arithmetic, loops and explicit borrowed buffers, with no general effects or captured authorities. Klara supplies code identity, world dependencies, guards and installation licence; metacarp supplies specialization, ownership, ABI lowering and machine code. Chez retains generic control and persistence. K3 is a representation stage; T3 is a certification/execution tier. Sending code to LLVM does not certify it.

**Cost:** medium for this subset, very high for a native runtime supporting persistent values, worlds and resumable frames. KRI explicitly requires all of those (`klara/doc/architecture.md:93–108`, K). C templates also remain part of the LLVM implementation; this is not a C-free backend (`metacarp/carp-llvm-backend/README.md:86–94`, U).

**Gains:** Klara avoids a second LLVM implementation; metacarp gains an interactive kernel workload and a reference execution oracle. **Concessions:** Klara accepts a restricted native subset and metacarp's ABI; metacarp accepts an embedding interface with immutable artifact lifetimes rather than letting its REPL's reset policy govern Klara. Published latency measurements support asynchronous compilation, not a permanent impossibility claim about future latency. RFC 0003 already requires generic execution while candidates are prepared (`klara/rfc/0003-licensed-specialization.md:53–65`, K).

### (c) Shared IR versus K1/K2 translation

**Recommendation: translation first, a common lower dialect only after two working consumers.** K1 can contain explicit CPS/frame operations; carp-ir has no `perform`, `handle`, world lookup or authority split constructor (`klara/doc/architecture.md:63–68`, K; `metacarp/carp-ir/carp-ir.carp:41–64`, U). Translate effect-free or fully effect-lowered K2 regions into resolved Carp core, run inference/specialization/ownership, then backend lowering. Later, a validated concrete import could target `SpecializedExpr` to avoid repeating inference.

The adapter must map de Bruijn locals to fresh `CoreRef`s and preserve left-to-right evaluation. World-dependent calls must become explicit parameters or guarded closed references. Map nil, booleans, arithmetic overflow, ratios and equality deliberately: Klara's datum and primitive domain is larger than Carp's machine scalar domain (`klara/doc/semantics.md:24–38,272–280`, K). For example, an integer-add kernel needs range evidence or a checked overflow/fallback protocol before it can replace generic addition.

**Cost:** medium for the scalar/buffer dialect; high for a universal IR with boxed values and continuations. Preserve source maps, CodeIds, target layouts and evidence dependencies in a versioned envelope. Its cache key includes compiler/Core revisions and target configuration, not only function source. Stable mangling already has one metacarp owner (`metacarp/carp-c-abi/README.md:3–8`, U).

**Gains:** Klara gets native code without abandoning K0; metacarp gets a reusable non-reader frontend. **Concessions:** Klara materializes layout and effect decisions before import; metacarp exposes and validates an import contract rather than promising internal constructors as a permanent API. Both give up the attractive but misleading promise that one early IR can express both languages unchanged.

### (d) Shared typed transformers and hygiene

**Feasibility: medium for shared protocols/checkers; low for one drop-in expander.** H correctly distinguishes checking transformer programs over forms from checking their generated programs. U remains explicitly unhygienic, compiles macro bodies at definition time, and resolves generated names as written (`metacarp/carp-expand/README.md:9–20,50–52`, U). Klara implements scope-set introduction and resolution, though its macros still receive ordinary data carrying metadata rather than a separate syntax-value kind (`klara/src/klara/expand.clj:5–15,196–210,470–479`, K; `klara/doc/guide/05-staging.md:298–299`, K).

Share a transformer invocation envelope: syntax payload, source provenance, explicit binding mode, declared input grammar, and recorded dependencies. Reuse the BAS checker for shape claims where its builtin semantics match. It cannot by itself prove hygiene, binding correctness or output typing. Its full-calculus branch has unmechanized obligations and an essential pruning step (`metacarp/docs/bas-calculus.md:1–33,372–384`, `origin/ct-set-theoretic`).

**Cost:** medium for schema/oracles, high for a shared transformer VM and scope-aware representation. **Gains:** Klara gets transformer diagnostics and corpus discipline; metacarp gets optional structured/hygienic syntax for new clients. **Concessions:** Klara accepts explicit unsafe capture for imported legacy macros; metacarp preserves legacy unhygienic behavior under a compatibility mode. Making Carp's existing macros hygienic by default would change program meaning and is not required for unification.

### (e) Value exchange, layouts and freeze

**Feasibility: high for scalars and flat buffers; medium to high cost for persistent graphs.** Carpaccio supplies a working seam, but not universal value equivalence. `SharedValue` is a mutable native view; its owner retention and Panama arena determine lifetime. `snapshot` copies to a persistent map (`carpaccio/src/carpaccio/shared.clj:286–320,354–358`, C). Current native wrappers conservatively borrow every shared record uniquely, using dynamic address-range loans (`carpaccio/src/carpaccio/runtime.clj:86–90,254–273`; `carpaccio/src/carpaccio/shared.clj:23–66`, C).

Specify four exchanges: immediate scalar conversion; scoped borrow of a native layout; transfer of an opaque owner with its deleter/generation; explicit immutable materialization. Borrowing requires layout identity, bounds, alignment, thread and lifetime evidence. Layout parity needs target facts: U queries clang and uses pointer-only wrappers for aggregate ABI coercions (`metacarp/carp-llvm-backend/README.md:46–63`, U).

Zero-copy freeze requires revoking all mutable aliases and retaining storage after region exit; a read-only view alone does neither. Otherwise copy explicitly. Persistent collection adoption also needs Klara equality/hash and sharing laws, not just identical bytes. A Panama arena belongs to JVM interop; it is not the portable storage contract. R usefully distinguishes storage handlers, roots, mobility and logical release from physical reclamation (`metacarp/docs/allocator-parametric-memory.md:30–52,117–136`, R).

**Gains:** Klara gets native mutation behind value semantics; Carp/carpaccio gain reusable lifetime and publication contracts. **Concessions:** Klara admits boundary copying and dynamic loans; native code obeys host leases, cannot retain borrowed JVM objects freely, and cannot mutate frozen storage. Both abandon universal zero-copy exchange.

### (f) Shared self-hosting discipline or kernel

**Feasibility: high for discipline, medium for a small implementation substrate, low for one semantic kernel.** U's fixed-point script compares generated C across successive metacarp generations, compiles strict C99, runs a smoke program and records provenance (`metacarp/scripts/check-fixed-point.sh:59–91`, U). The broader harness also runs phase/reference/expansion/sanitizer checks (`metacarp/README.md:200–242`, U). Equality of emitted C is a reproducibility check; it cannot establish compiler correctness or exclude a compromised seed.

Adopt matching bootstrap manifests, deterministic IR serialization, explicit generation naming and an independently executable corpus. Add diverse compilation where feasible; hashing a seed is provenance, not independent validation. Klara's self-specialization remains a research trajectory, not a prerequisite for a direct compiler (`klara/doc/architecture.md:166–176,208–216`, K).

A shared native library for syntax storage, deterministic IDs, graph algorithms and checked import is plausible. A shared semantic kernel is harder: metacarp implements Carp inference and destruction, while Klara's ansatz kernel checks proofs about a different calculus. Neither compiler's self-hosting makes its ownership pass a proof kernel (`klara/doc/semantics.md:185–201`, K).

**Cost:** low to medium for shared release discipline; high for common compiler implementation. **Gains:** both obtain reproducible artifacts and cross-language tests; Klara could eventually compile its compiler's closed regions through metacarp. **Concessions:** both constrain build nondeterminism and maintain independent bootstrap paths. Klara must retain certificate rechecking; Carp need not acquire proof dependencies merely to serve as its backend.

## 3. Genuine incompatibilities and their limits

**Static rejection versus dynamic acceptance is fundamental at the language boundary.** Carp's existing inference cannot accept every successful untyped Klara program. A boxed interpreter can encode dynamic behavior, but that adds a runtime rather than establishing static narrowing. Keeping generic execution makes this compatible at system level; requiring every Klara program to pass ordinary Carp inference would surrender Klara's core contract.

**GC versus ownership is primarily representation engineering.** Runtime-managed persistent nodes and affine native owners can coexist behind handles and leases. Replacing `free` with a no-op does not implement GC: roots, safepoints and relocation cooperation remain necessary. Klara already anticipates native RC/arenas alongside tracing GC (`klara/doc/architecture.md:95–98`, K). H's assertion that Klara pays none of the native deallocation cost ceases to hold once it adopts native regions.

**Multi-shot effects versus native mutable frames require real semantic work.** Carp's repeatable closures do not provide capture of the caller's control context. Heap frames/CPS are engineering; duplicating a live exclusive loan or unique external resource is fundamentally invalid without a split/clone protocol. Never capture through an ordinary Panama/C frame. RFC 0002 already specifies a detected opaque boundary and selective CPS (`klara/rfc/0002-effects-and-handlers.md:28–47`, K).

**Forks versus affine resources require kind-specific laws.** A file cannot be independently transferred to two branches. Random streams can split; evidence requires mass conservation; immutable data can share. Current T0 refuses captured resource/evidence authorities on repeated resume, rather than providing a universal split escape hatch (`klara/rfc/0001-forks-and-authority.md:87–95`; `klara/src/klara/eval.clj:792–825`, K). A native call should initially complete its loan before any fork-resume point.

**Worlds versus compiler sessions are engineering with a semantic constraint.** Carp session replacement replays dependents and can clear native publication; Klara requires simultaneously callable old/new pinned worlds. Exported immutable generations, explicit dependency closures and delayed unloading bridge this gap. Sharing one mutable global namespace cannot.

**Certification versus testing is a trust incompatibility, not an implementation detail.** Backend parity and contract observers falsify bugs; they do not license check erasure by theorem. RFC 0003 distinguishes proved, guarded and tested licences (`klara/rfc/0003-licensed-specialization.md:57–69`, K). Retaining a fallback cannot repair memory corruption after an unsound native call: preventive boundary validation and a trusted or proved lowering remain necessary.

## 4. First collaboration step, recommendation and falsifiers

**Christian and Veit should first work through one externally rooted store by hand, then agree a tiny boundary-contract test matrix.** This directly serves #74's arena design and Klara's native isolation boundary. It is more informative than immediately writing a shared compiler.

I read [RFC #74](https://github.com/cyberwitchery/metacarp/issues/74) and its comments with read-only `gh`. The retrieved issue reports activity through October 11, correcting H's October 9 cutoff. Veit explicitly requests design discussion, rejects outsourcing that thinking, and objects to both externally rooted stores and a second authority scheduling frees. His [October 8 response](https://github.com/cyberwitchery/metacarp/issues/74#issuecomment-6054755660) and [October 9 follow-up](https://github.com/cyberwitchery/metacarp/issues/74#issuecomment-6077266822) govern the collaboration format. This note is private preparation, not a comment to paste. Nothing was posted.

Use a parent-owned record containing an array and a helper that stores an arena-born string through a reference to that array. Compare direct access, a forwarded parameter, a projected field and an unknown callback. For each, Christian and Veit should draw the roots, identify the allocation provenance, map the callee's Store target back to the caller, and name exactly which plan operation destroys each value. Include a moved-in outside allocation: resetting arena storage must not suppress destruction of its external contents. Separate the safety decision from copy-out policy.

The reviewable outcome should be a small human-authored table of accepted/rejected/unknown cases, including a valid store into an arena-local container, and a decision on whether argument-root summaries suffice or projected places are needed now. Christian can independently reconstruct a counterexample and discuss that reasoning in his own words. Veit retains ownership of Carp policy. Only after agreement should implementation produce fixtures and a versioned machine-readable report consumed by metacarp and carpaccio. Klara then adds a closed scalar/buffer kernel adapter; defer universal IR, hygienic Carp defaults and shared-kernel work.

The main claims have explicit ways to fail:

| Claim | Falsifier or decision gate |
|---|---|
| Existing ownership machinery can help erase local authority checks | On the same admitted region, dynamic and erased T0 traces differ in settlement, cancellation, budget or authority reuse; keep checks until the discrepancy is explained. |
| K2 translation is a useful unification seam | A small effect-free scalar/buffer corpus requires changing Carp semantics or bypassing ownership validation; retreat to an explicit foreign-kernel interface. |
| The native path preserves Klara observations | Differential execution diverges on overflow, truthiness, equality, evaluation order or an intercepted ambient effect; narrow the admissible subset. |
| Boundary summaries prevent arena escape | An admitted direct/forwarded/projected store leaves an arena pointer reachable after reset, or valid local stores become systematically inexpressible; revise provenance/precision. |
| Generations support pinned worlds | After redefining a callee, an old pinned closure calls new code, sees changed layout, or reaches unloaded code/deleters; prohibit installation until lifetime tracking is fixed. |
| Freeze permits value sharing | Any retained alias mutates an adopted frozen value, or region close invalidates it; use explicit copying instead. |
| Bootstrap sharing reduces trust and maintenance cost | Repeated deterministic builds differ, independent compilation disagrees, or shared release machinery forces synchronized semantic changes; retain separate seeds and manifests. |

These gates make “one system” concrete: one installation and evidence boundary, two compatible execution regimes, and independently testable translations between them.
