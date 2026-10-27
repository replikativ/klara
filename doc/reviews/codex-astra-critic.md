# Klara iteration 1: critical review

Reviewed 2026-10-27. **Verdict: a promising research architecture, but not yet a coherent v1 specification.** The strongest idea is a persistent, basis-pinned execution environment that makes definitions, expansion dependencies, and inference experiments inspectable. The largest risk is treating resource safety, approximation correctness, and hosting as consequences of that architecture when each needs an independent contract.

I read the design-space document, synthesis, and A–E notes in the requested order, then inspected relevant implementation files and primary literature. References below use `01-core-v1.md` and `research/…` relative to `doc/klara/`; `v0/…`, `lean/…`, and `doc/…` are relative to the lambda-join repository. Sibling paths are relative to `Development/`. Code findings are from inspection, not newly executed benchmarks. Several research-note line references have drifted: current `v0/src/v0/defs.clj` has 138 lines. Severity means **high**: threatens a central guarantee or v1 viability; **medium**: substantial specification or implementation work; **low**: clarification or presentation.

## 1. Soundness and coherence

### High — Dynamic tags do not enforce the proposed resource discipline

The core permits unrestricted variables and application, while sorts are checked “at fork and at copy” (`01-core-v1.md:43–49,75–83,296–306`). What operational event is a copy? `(let [r (open …)] (pair r r))` duplicates a reference without invoking a named copy operation. A persistent map containing an array is not transitively immutable. A closure with no lexical resource captures can still obtain a resource through `resolve` or an installed handler.

Classifying every persistent collection as Value conflicts with deriving closure copyability from captures. The rule must apply transitively to collections, syntax payloads, metadata where accessible, handler environments, and continuation frames. A single four-way tag also cannot describe a record containing both evidence and a branchable cell: its fork operation is a product of different protocols.

**Fix:** distinguish immutable data, resource references, and authority to consume/branch/settle resources. Introduce an operational resource store with generation/ownership checks, explicit move/borrow/consume rules, and aggregate footprints. Alternatively, explicitly permit aliased references but prove *authority* non-duplication; that is a different, often more practical promise than affine objects. Static affine checking can erase dynamic checks later. Arbitrary Java objects and opaque Clojure closures must default to an opaque capability boundary, not receive optimistic structural certification.

Evidence needs the same separation. Copying an observation's bytes is harmless; counting its likelihood twice is not. Fit/holdout permissions and spending rights should be controlled tokens referencing copyable data. This accommodates repeated likelihood evaluation and cross-validation without pretending that numbers themselves are linear (`research/E-resources-learning.md:259–263,303–309`).

### High — A1's probabilistic target is not closed under the language

`H_meas` targets finite discrete subdistributions, yet the language includes unrestricted recursion and `factor` (`01-core-v1.md:44,60–69`). A geometric recursive sampler has countably infinite support despite every individual choice being finite. A factor of 2 produces mass 2, not a subdistribution. Restricting factors to [0,1] would repair the second issue but materially restrict inference.

**Fix:** initially define finite execution trees with nonnegative weights; take increasing limits for recursive programs, allowing countable support and potentially infinite total mass. Define normalization separately, with explicit zero/infinite-mass failure. Alternatively, scope v1 adequacy to bounded terminating programs and say so. The separation of scoring and normalization in [Staton et al., *Semantics for probabilistic programming*](https://arxiv.org/abs/1601.04943) is directly applicable.

A1 also compares unlike objects unless “denotation” already means its observable projection. Specify `observe(denote(e, basis, host)) = operational-observation(e, basis, host)`. Observations must distinguish returned values, language errors, divergence, and relevant external traces. A host oracle that merely returns answers does not specify irreversible writes. Fix handler order: state-inside-choice and choice-inside-state generally produce different sharing behavior. A deterministic total `step` is possible over a reified exploration machine, but `Config → Option Config` alone does not explain probability weights or oracle transitions (`research/A-core-calculus.md:190–211`).

### High — Code identity is being confused with closure identity

The hash of a canonical body cannot identify a closure's behavior (`01-core-v1.md:107–113`). `(make-adder 1)` and `(make-adder 2)` may have the same body but different environments. Globals introduce another choice: is a closure linked to its creation basis or the caller's current basis? Neither answer follows from hashing source.

**Fix:** separate `CodeId`, closure value, and executable specialization. `CodeId` identifies canonical syntax; a closure additionally has captures and an explicit global-resolution policy; an executable carries guards and an origin identifier. Either prohibit general closure equality or specify equality using these components, with resource-containing closures excluded from structural equality. Preserving origin identity permits optimization, but making reflection an effect does not make its observations disappear.

A2 needs typed equations with parameters: `run(specialize(p,a),b) ≈ run(p,(a,b))`, under the same basis and handler interpretation. Equality here is observational, not α-equality of residual programs. A fixed-width hash is never mathematically injective on unbounded syntax: use canonical syntax identity in the theorem, collision resistance or collision checking in the implementation (`research/A-core-calculus.md:198–207,224`).

### Medium — The categorical direction is plausible, not an established model

Keeping copyable code separate from non-copyable authority is sensible. But “an MC acting on a linear world” does not specify the action, its laws, or what “natural in Δ” means when programs allocate and destroy resources (`01-core-v1.md:16–20,68–71`). Resource contexts may change shape; a fixed `Δ → Δ` interface needs an explicit store interpretation or indexed alternative.

[Benton's mixed linear/non-linear model](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-352.html) provides a disciplined comparison, not an automatic theorem for an MC, whose copy structure need not be cartesian. Likewise, quote/run syntax does not by itself establish every universal-evaluator requirement of [Pavlović's MC](https://arxiv.org/abs/1208.5205). Build the operational authority invariant first; model the pure data fragment second; leave the action theorem explicitly open. The existing Lean result is useful but concerns a first-order, footprint-typed fragment with weights elided (`lean/LambdaJoin/Core.lean:1–23`), not this dynamic higher-order runtime.

## 2. Feasibility and cost

### High — Continuations are the missing architecture experiment

Kernel-v0's `perform` calls a function and `handle` merges a map (`v0/src/v0/kernel.clj:373–386`). There is no captured continuation. Thus “80% of Core v1” by forms (`research/A-core-calculus.md:239`) badly understates the remaining engineering. JVM-hosted general resumptions require transformed code, explicit frames, or another runtime strategy; ordinary IFn calls do not supply resumable host frames.

The hard case is Klara → linked Clojure → Klara callback → effect. Capturing through the intervening untransformed host frame cannot be promised as zero-overhead interop. Document a boundary error, a callback-specific transformation, or a restricted synchronous protocol. Virtual-thread scheduling would not itself provide arbitrary multi-shot continuation cloning.

**Fix:** use direct calls for non-suspending/tail-resumptive operations, explicit heap frames or selective CPS for resumptive code, and an opaque host boundary. Benchmark this before custom maps. [Koka's generalized evidence passing](https://www.microsoft.com/en-us/research/wp-content/uploads/2021/03/multip-tr-v2.pdf) offers concrete fast paths. [OCaml's handler implementation](https://arxiv.org/abs/2104.00250) demonstrates how much runtime work is needed even for one-shot continuations; its low overhead is evidence for its implementation, not a JVM forecast.

Multi-shot admission is inconsistent across the notes: A excludes resources and world state, the synthesis excludes resources/evidence, and B permits branching branchable objects (`research/A-core-calculus.md:186; 01-core-v1.md:65–66; research/B-memory-model.md:261–266`). Define a distinct **fork-resume** that branches the captured store and splits authority. Merely cloning immutable control frames can still replay future I/O. Inference needs an effect/replay contract as well as a capture-footprint check.

### High — Basis-aware optimization needs versioned caches, not one mutable target

Pinned global reads currently perform map lookups (`v0/src/v0/world.clj:51–54,105–110`). This can dominate tiny functions, but it need not remain an every-read cost: cache resolution in a basis-specific execution environment and inline immutable targets. Old and new bases must coexist. A single latest-world call-site target cannot serve both without a basis/version guard (`01-core-v1.md:124–131`).

There is a concrete warning in the prototype: the “winner-hash firewall” compares only winning **patterns** (`v0/src/v0/dispatch.clj:101–108`). After warming a cache, `extend-op!` with `:force true` can replace the implementation at the same pattern while invalidation retains the old cached `:impl` (`:154–178`). This follows from inspection; I did not run a reproducer. Fix winner identity and version the table before using this prototype as evidence for incremental dispatch correctness.

Linked Var watches are also incomplete as stated (`01-core-v1.md:161–162`). The local Clojure `Var.unbindRoot` changes the root without notifying watches (`clojure/src/jvm/clojure/lang/Var.java:295–298`); `bindRoot` publishes before notification (`:278–284`). Define supported mutations and concurrent visibility, or retain root/version validation. “Watches invalidate” is not a complete correctness protocol.

### Medium — Tags, tokens, and O(1) forks hide different costs

Do not add a wrapper to every Clojure value. Primitive/class-level classifications can be cheap, but certifying arbitrary nested host collections requires traversal or trusted summaries. New Klara aggregates can maintain compositional footprints at construction; imported objects need validation. Measure allocation, retained heap, and admission scans, not only call overhead (`01-core-v1.md:299–301`).

Region ownership must cover aliases within a branch, not just prevent token escape. If an older persistent root remains observable, mutating its token-owned nodes is unsound even without a fork. O(1) revocation applies to a cooperating representation, not conversion of an arbitrary foreign array or native arena (`research/B-memory-model.md:238–240,321–322`).

An O(1) snapshot-root operation is credible; O(1) end-to-end fork across arbitrary resources, disk, and remote services is not (`01-core-v1.md:88–90`). Separate logical fork, durable publication, resource branching, and subsequent copy debt. The SMC measurements are useful exploratory evidence, including the transient regression at one write, but exclude the proposed handler and tagging machinery (`research/B-memory-model.md:350–373`). They do not yet predict language performance.

## 3. The narrowing doctrine

### High — There are three contracts here, not one erasure theorem

The §11 checked-default decision supersedes §5 and Q11, which still say hints are default (`01-core-v1.md:146–150,230,255–263`). Reconcile the normative text rather than requiring readers to execute a decision log.

Use three separate statements:

1. **Hints:** erasure preserves observable behavior, including effects; speculation must not repeat an already performed effect on fallback.
2. **Checked claims:** successful execution preserves the corresponding unannotated result; increased precision can introduce designated check failure, with a defined precision relation and error ordering.
3. **Approximation permissions:** explicit contracts admit a set of implementations under a specified metric or statistical guarantee.

The second resembles the [SNAPL gradual guarantee](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SNAPL.2015.274); cheap guards alone do not establish it. If blame is caught by ordinary `try`, an annotation can change a returned value through the recovery branch. State whether the guarantee excludes contexts that catch blame or relates those contexts explicitly. “Never change meaning” is too strong without this qualification.

Shallow checking is insufficient to license deep representations: checking “vector” does not justify an unboxed integer vector, and checking “callable” does not justify its return representation. Specify guarded projections, element validation, or higher-order contracts. A proven representation change must preserve overflow behavior, equality, hashing, and exceptions. Converting integers to doubles is not merely layout selection. The dispatch-pattern/annotation distinction is correct and should remain syntactically explicit.

### High — Approximation is not generally substitutive in arbitrary contexts

`within ε` cannot simply weaken global equality to “up to ε” (`01-core-v1.md:193–199`). Two numbers differing by 10⁻⁶ can produce entirely different results under a threshold branch. Error composition needs metrics and contextual sensitivity; discontinuous contexts may admit no useful bound. Preserve exact core semantics, but make `within` an explicit approximation boundary with an observation contract. Require exact behavior outside it or an explicit propagation of uncertainty.

“Proved or measured ε-adequate” conflates guarantees. A measured discrepancy on selected inputs is neither a universal bound nor automatically a confidence guarantee. Distinguish certified bounds, statistical bounds with assumptions and failure probability, and predictions. Adaptive stopping and repeated model selection require corresponding statistical validity; disjoint IDs alone do not establish independence.

### High — Convergent meaning conflates limits, relations, and policies

Scott approximation is ordered information approximation; numerical iteration need not be monotone or convergent. A deterministic iteration has at most one limit in a metric space. Multiple training solutions arise from different initializations, randomness, or admissible solution specifications, not a single trajectory having several limits (`01-core-v1.md:280–294`).

For a contraction with constant `q < 1`, a residual can justify `distance(x,x*) ≤ distance(x,F(x))/(1−q)`. Without such assumptions, a tiny step or gradient does not bound solution error. A learned convergence predictor cannot certify the missing premise.

**Fix:** expose an approximant stream yielding `(value, certificate-or-estimate)`, plus a stopping policy. Keep a solution relation distinct from a chosen exact trajectory. Budget exhaustion may return an explicit uncertified result, raise a condition, or continue; it cannot silently satisfy a hard tolerance. Put general `converge` in an experimental library until one contractive numerical example and one probabilistic example have precise observations and stopping rules.

## 4. Staging and “macros as two constructs”

### High — The split is useful, but functions over code are not automatically compositional

§13 improves the vocabulary, but “compositional because they are functions” bypasses code binding, generativity, effects, and phase availability (`01-core-v1.md:322–339`). A generator can save code containing a local binder into a mutable cell and splice it after the binder's scope ends. An input grammar cannot prevent that.

Separate datum quotation, syntax quotation, open code, and closed executable code. The core's `(quote d)` is a literal, not automatically §13's staging bracket (`:43,315–316`). A global basis cannot close arbitrary lexical variables, contrary to the loose suggestion in `research/C-staging.md:139–146`. `lift` also needs restrictions: lifting an open file or resource-capturing closure must not turn it into copyable, serializable code.

The comparisons suggest concrete mechanisms:

| Precedent | Take for Klara | What the two-construct split does not supply |
|---|---|---|
| [Racket scope sets](https://users.cs.utah.edu/~mflatt/scope-sets-3/) | Binding-aware syntax, explicit expansion contexts, local expansion | Binding interfaces for generated definitions and controlled intentional capture; grammar alone is insufficient |
| [Lean 4 elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/) | Separate syntax rewriting from context-sensitive elaboration | Access to expected types, local context, constraints, diagnostics, and postponed work; an output-language label is much weaker |
| [Scala 3 quotes](https://docs.scala-lang.org/scala3/reference/metaprogramming/macros-spec.html) | Quote/splice staging rules and scope tracking | Cross-stage availability and escaped-quote checks, even when generated code has a type |
| [BER MetaOCaml](https://okmij.org/ftp/ML/MetaOCaml.html) | Safe code constructors, dynamic scope-extrusion checks, controlled cross-stage persistence | `code<τ>` alone does not settle effectful generation or transport of captured host values |
| [Template Haskell](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/template_haskell.html) | Explicit generation context and declaration staging boundaries | Generated declarations, reification, and compile-time execution order still need a dependency/phase model |

**Fix:** retain two public APIs over one syntax/code library. Give syntax extensions binding declarations and an expansion-context capability; give staged functions a checked `close/run` boundary. Optional typed staging should use the same runtime scope checks, adding static rejection. Type-directed elaboration that selects different operations is meaning-defining elaboration, not an erasable annotation optimization.

### Medium — Recorded macro effects do not automatically make expansion reproducible

Recording a file content hash requires an identity and revalidation protocol for that file. Recording an LLM response makes that response replayable, but does not make a fresh request under the same basis deterministic (`01-core-v1.md:252–254`). External inputs need versioned snapshots or recorded-response handles; volatile effects must disable cache reuse. Missing bindings and negative lookups are dependencies too.

Deterministic scope IDs derived from parent hash and binder path need a generative invocation identity when independently produced expansions are composed (`:114–115`). Canonicalize afterward, preserving binding relationships. Test repeated cached insertion, nested local expansion, and mutually recursive syntax definitions. Also reject cache cycles cleanly. Keep the excellent distinction between re-expansion as a new definition and specialization as a transparent implementation change.

## 5. Missing v1 contracts

### High — Concurrency, cancellation, and irreversible effects are release blockers

Non-copyability does not define concurrency. Specify at least structured task lifetimes, cancellation points, dynamic-binding inheritance, basis inheritance/raising, resource transfer, and whether branch/join is concurrent or merely logical. A snapshot guarantee must include publication ordering. A standalone `releaseFence` is not a complete cross-thread publication protocol; specify the communicating release/acquire or volatile operation ([Java VarHandle specification](https://docs.oracle.com/en/java/javase/25/docs/api/java.base/java/lang/invoke/VarHandle.html); `research/B-memory-model.md:273–274`).

World updates already show why this matters: root update and cell synchronization are separate (`v0/src/v0/world.clj:85–90`). Concurrent writers can publish root A, then root B/cell B, then stale cell A. This is an inspection-derived interleaving, not a measured failure. Use a single versioned publication protocol.

Define I/O as replayable reads, buffered transactional writes, or irreversible effects. Fork rejection, retries, cancellation, and commit must preserve that classification. The existing transactor can rerun its body (`world.clj:116–144`), so sending a message inside it cannot be treated like updating a map. Multi-shot continuations need deterministic cleanup on abandonment and exactly-once settlement of branch handles.

### High — Errors and authority need a minimal specification

Encoding exceptions as `:exn` leaves unanswered: resumable condition versus abort, handler-clause failure, double resume, finalization, cancellation during cleanup, host exception translation, and source-level stack reconstruction (`01-core-v1.md:52–63`). Define named errors and a cleanup protocol now; a sophisticated restart system can wait.

Handlers are not automatically a security sandbox. Say which capabilities authorize filesystem/network access, expansion effects, loading code, and spending budgets. Hashes establish content identity, not trust. Trusted linked libraries can remain an explicit escape hatch, but imported host references must not silently acquire fork-safe status.

### Medium — Modules, numerics, and observability cannot remain implicit

Extension ownership requires stable module identity distinct from a changing revision hash (`01-core-v1.md:144–145`). Specify namespace aliases, imports, dependency manifests, mutually recursive groups, initialization effects, and owner identity across forks. Otherwise a normal module edit changes its “owner” or fresh imports silently change resolution.

Define the numerical tower, overflow, division, NaN/signed-zero behavior, promotion, and reduction-order guarantees before using numerical specialization as a selling point. Specify RNG algorithm/version, stream addressing, and reproducibility under scheduling. The mention of counter-based generators “or SplitMix” conflates different constructions (`:310–312`); splitting needs a documented statistical contract, not a claim of literal probabilistic independence.

Debugging needs source spans through expansion, async continuation traces, displayed basis IDs, macro dependency explanations, and “why did this deopt?” inspection. These are essential to a REPL whose definitions have several simultaneously live versions. Full distributed placement, automatic convergence prediction, and persistent learned optimization are **low-severity omissions for v1** and should be deferred.

## 6. Alternatives and overlooked lessons

### Medium — Borrow mechanisms and proof boundaries, not an omnibus feature list

Much of the named literature is already present in A–E. The problem is insufficiently importing its restrictions.

- **Koka/Effekt:** use a handler-oriented IR with explicit capabilities and suspension information; retain a dynamic source language. [Effekt's contextual effect polymorphism](https://se.cs.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf) is especially relevant to higher-order callbacks without repetitive effect annotations. Lexically scoped capability routing would be a deliberate semantic choice, not a transparent implementation of arbitrary dynamic handlers.
- **Unison:** separate immutable definition identities from human names and namespace evolution. Its [hash model](https://www.unison-lang.org/docs/language-reference/hashes/) is a stronger starting point for modules than “hash expanded source.” Klara must additionally decide whether dependencies are fixed content references or basis-relative names.
- **Julia:** borrow the formal separation of running-world visibility from newly defined methods, including explicit escape points ([world-age semantics](https://arxiv.org/abs/2010.07516)). A forked world requires a more general version relation than a scalar epoch, but does not remove the visibility problem.
- **Self:** treat deoptimization as reconstruction of a valid source-level state, not merely swapping a function pointer ([dynamic deoptimization](https://bibliography.selflanguage.org/_static/dynamic-deoptimization.pdf)). Entry-only fallback is a reasonable v1 limit; a loop checkpoint after I/O must resume from state, not restart the invocation.
- **Granule:** borrow parameterized grade algebras with their typing rules and laws ([graded modal types](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)). A product of numbers is not yet a resource calculus. Time `max` models ideal span, not observed runtime under contention; peak memory needs liveness/overlap information, not indiscriminate addition (`research/E-resources-learning.md:248–253`).

These choices support a narrower implementation: a CEK-style reference machine, selective continuation compilation, immutable versioned definitions, and an explicit inference handler. That is enough to test the distinctive thesis without simultaneously building a new collection runtime and general resource-rational optimizer.

## 7. Positioning

### High — Both audiences will reject unsupported guarantees before missing features

PL researchers will first challenge the resource invariant, the measure domain, the untyped-to-linear interpretation, and the use of “gradual guarantee” without a precise relation. They will also distinguish scoping preservation from resource safety: naming every stuck state an error makes progress easier, but proves little about authority conservation (`research/A-core-calculus.md:222`). Give them one small mechanized theorem with explicit exclusions.

Clojure users will first encounter altered redefinition visibility, opaque-host restrictions, lazy sequence resource classification, and uncertain exception/debugging behavior. “Zero overhead” will sound implausible beside those changes. Give them a familiar collection ABI and a compelling workflow: fork a running simulation, edit its model in isolation, compare results, and deliberately adopt a version. Publish latency and allocation costs for that workflow.

Do not defer the value proposition entirely (`01-core-v1.md:272–276`). Defer the exhaustive language comparison, but write the v1 promise now: **a forkable, inspectable execution environment for simulation and inference, embedded in the Clojure ecosystem**. This is differentiated and testable. General-purpose replacement-language ambitions can follow evidence.

## 8. Prioritized changes and uncertainty-reducing experiments

### Document changes, in implementation order

1. **High — Rewrite §§1–2 and §12's sort paragraph around an operational authority invariant.** Define aggregates, aliases, host opacity, resource lifecycle, and fork-resume. This is prerequisite to every safety claim.
2. **High — Repair A1/A2 and identity (§§1,3).** State observation domains, handler order, weighted recursion, code versus closure identity, basis policy, and collision assumptions. Restrict the first theorem to a named fragment.
3. **High — Reconcile §§5,7,11–12.** Checked claims are default; hints preserve traces; approximation is an explicit contract. Keep estimates outside certification. Move general convergent meaning to experimental status.
4. **High — Add a JVM execution/interop contract (§6).** Specify transformed regions, opaque callback boundaries, one-shot checks, and basis-versioned targets. Replace blanket zero-overhead claims with measurable paths.
5. **High — Add minimum task, cleanup, I/O, and publication semantics.** These cannot safely be retrofitted after resource behavior becomes public.
6. **Medium — Expand §13 with code categories and binding contracts.** Specify close/run, lift restrictions, generativity, local expansion, phase dependencies, and effectful input replay.
7. **Medium — Add module identity, numeric behavior, and debugger metadata.** These determine dispatch ownership, stable content identity, and useful diagnostics.
8. **Medium — Rewrite §10 around semantic risk.** Make continuation and authority experiments precede new maps and cross-runtime performance comparisons. Treat size estimates as hypotheses, not commitments.

### Experiments, each with a decision criterion

1. **High — Dynamic-authority adversarial suite.** Exercise duplicate locals, nested resource collections, metadata, escaping closures, resource lookup after capture, repeated resume, and cancellation. Pass only if the reference machine rejects unauthorized consumption/branching and settles handles once. Mechanize that invariant before the full MC action.
2. **High — JVM continuation matrix.** Compare direct style, explicit frames, and selective CPS for tail effects, one-shot suspension, enumeration, and SMC resampling. Include nested handlers, exceptions, and host callbacks. Report allocations per capture, retained bytes per particle, throughput, and p99 latency. If host-frame capture is unsupported, make that a tested boundary error.
3. **High — Basis/cache litmus tests.** Two fibers retain different bases while a macro and dispatch method change; warm the same-pattern dispatch cache; unbind a watched Clojure Var; race two world writers. Assert each fiber's specified observations, not merely cache-hit counts. This directly tests the proposed speed/correctness bargain.
4. **High — Annotation and approximation differential tests.** Strip hints and compare effect traces; add checked claims and test the stated blame relation, including catches. Test overflow, lazy values, threshold branches, and fallback after I/O. For convergence, compare a certified contraction with a misleading small-residual example. Estimated error must never be accepted as a hard bound.
5. **Medium — Staging composition corpus.** Insert cached expansions twice, splice escaped local code, generate recursive bindings, lift an opaque closure, and change an external macro input. Cached expansion must agree with fresh expansion under the same complete input manifest, modulo binding-preserving canonicalization.
6. **Medium — Integrated workload before runtime proliferation.** Run one realistic forked simulation with basis reads, continuations, checks, and optional receipts. Vary write density and resampling duplication; report allocation and memory as well as time. Compare persistent collections, region reuse, and clone-on-duplicate on that identical workload. Only then decide whether Koka/Lean-style owned memory merits a separate runtime.

The criterion for v1 should be a demonstrably correct, usable fork-and-inspect workflow. The broader categorical and learning agenda becomes more credible when it is built on that executable boundary.
