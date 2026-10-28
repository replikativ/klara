# M. What staging must provide for a V8-class JIT (research note, 2026-10-28)

Research note, Klara iteration 1. It builds on `README.md`,
`doc/architecture.md` (§3 tiers, §4.2 the compiler under its own staging
lens, §6 the predictor ladder, §8 the guarded-specialization square),
`doc/guide/05-staging.md`, `01-core-v2.md` §6 and §10 (gates R1–R8),
research notes C (grades, invalidation protocol §4.3, obligations O1–O12)
and D (call-site lattice, protectors), and the study
`lambda-join/studies/v8.md`, whose findings (dependency taxonomy, protector
cells, deopt-loop scars) are not repeated here. V8 was read at
`../v8` checkout `5fe0aa3bc79` (2021-10-25); Klara at its working tree
(`src/klara/stage.clj`, `world.clj`). Nothing was run. Status markers:
**Holds**, **Conj**, **Open**, **Refuted**.

## 1. Disagreements first

**M-D1. The V8 tree does not contain Maglev or Turboshaft.** The checkout
predates both and predates `src/execution/tiering-manager.cc`; the tiering
logic is `src/execution/runtime-profiler.cc`. The mid tier present is
Turboprop (`src/flags/flag-definitions.h:672-687`, `CodeKind::TURBOPROP` in
`src/objects/code-kind.h:31`, `PipelineImpl::OptimizeGraphForMidTier` in
`src/compiler/pipeline.cc:2822`), which V8 later deleted and replaced with
Maglev. Statements below about Maglev (SSA graph built straight from
bytecode plus feedback, compile speed between Sparkplug and TurboFan) and
Turboshaft (a CFG IR replacing sea-of-nodes in TurboFan's back half) are
from V8's public writing, not from this tree, and are marked *out-of-tree*.
If file:line evidence for them is required, the checkout must be updated.

**M-D2. "Deopt = guard failure → generic path" is only the weakest of V8's
deopt forms.** Klara checks guards on entry only, "never later — live frames
cannot be converted, so failure means the generic path runs from the start"
(`stage.clj:14-15`). V8 can leave optimized code at *any* deopt point:
each point carries a translation from machine state to an interpreter frame
(`src/deoptimizer/translation-opcode.h:16-42`: `INTERPRETED_FRAME`,
`CAPTURED_OBJECT` for allocations removed by escape analysis,
`BUILTIN_CONTINUATION_FRAME` for inlined builtins, `UPDATE_FEEDBACK`), and
the deoptimizer materializes the frames (`deoptimizer.cc:839`,
`DoComputeOutputFrames`; `:1009`, `DoComputeUnoptimizedFrame`). Entry-only
guards forbid speculation inside a loop body and after any performed
effect, which is where speculation pays. Klara needs mid-body deopt.

**M-D3. But Klara does not need V8's lazy deopt for world edits.** V8 must
kill *running* code when an assumption breaks: it marks dependent code and
rewrites return addresses of every live activation to a deopt trampoline
(`ActivationsFinder`, `deoptimizer.cc:245-290`). Klara's fibers run against
a pinned basis; an executable that was valid for root r stays valid for r
forever, and R4 requires that old versions keep running. Stack patching is
therefore unnecessary, provided assumptions are only taken on world cells
and immutable data (M-P2). This is the largest simplification Klara has
over V8, and it is not stated anywhere in the design yet.

**M-D4. "Guards = map checks" conflates two V8 currencies, and Klara
implements the expensive one for both.** V8 separates *runtime checks*
(`CheckMaps`, `src/compiler/simplified-operator.h:938`; the deopt-reason
catalogue) from *compilation dependencies* that cost zero instructions in
the code and are pushed on the writer side
(`compilation-dependencies.cc:887-913`, `Commit`; dependency groups stored
on the map itself, `src/objects/code.h:770-801`, `map.h:181`). Klara's
`[:world sym value-id]` guard is re-checked at *every* entry, for every
free global, with a linear scan over candidate executables
(`stage.clj:80-83`, `:159`). V8's push model is not the answer either: it
does work proportional to the number of dependents at publication, which
gate R1 forbids. The right realization is a third one (M-P2): validity as a
memoized predicate on roots.

**M-D5. Feedback is not predictor level 3.** Level 3 is "profiling and
sampled measurement, ms–s" (`architecture.md:268`). V8 feedback costs
nanoseconds per operation, is always on in the lower tiers, and is the
*only* source of speculation for the optimizing tier. It belongs on the
ladder as its own rung, inline feedback (call it 3a), below sampled
measurement (3b). Principle 5 (`architecture.md:287`) holds unchanged:
feedback steers, a guard licenses.

**M-D6. On the JVM Klara should not build a TurboFan.** HotSpot already
profiles, speculates, inlines, deoptimizes and performs OSR on whatever
bytecode Klara emits. The "JIT inside out" on the JVM is a world-level
specializer above HotSpot, and the V8 machinery of frame translation and
OSR is needed only for transitions out of and into T0 and on hosts without
a speculating JIT (Chez). §5 develops this.

Minor: the brief cites "§8 the compiler under its own staging lens"; in
the current `architecture.md` that is §4.2 (`:178`), and §8 holds the
commuting squares.

## 2. Mechanism mapping

| V8 mechanism | Evidence | Klara concept | Status in Klara |
|---|---|---|---|
| Ignition: register/accumulator bytecode interpreter, compiled lazily | `interpreter-generator.cc`, `bytecodes.h:72` | T0, CEK interpreter of K0 | **present** (`klara.eval`) |
| Sparkplug: 1:1 bytecode → machine code, no IR, no speculation, same frame layout as Ignition | `baseline-compiler.cc:293`, `:465`, `:1901-1925` | T1, generic code with var indirection | **missing** (design, `architecture.md:121`) |
| Turboprop / Maglev (out-of-tree): cheap speculation from feedback | `pipeline.cc:2822`; flags `:672-687` | T2, specialized code with guards | **partial**: cache and entry guards exist; no feedback-driven specializer |
| TurboFan: sea-of-nodes, inlining, typing, escape analysis, deopt everywhere | `pipeline.cc:1320-2183` (phases), `:2697` | T2 on Chez; T3 for law-licensed rewrites | **partial**: one T3 rewrite (S3) |
| Feedback vector per closure-literal site; IC lattice with cap 4 | `feedback-vector.h:31-66`; `globals.h:935-952`; `ic.cc:667-676`, `:692-697` | level 3a evidence keyed by (CodeId, site) | **missing** |
| Runtime check (CheckMaps etc.) | `simplified-operator.h:938` | `[:arg i pred]` guard | **partial**: entry only |
| Compilation dependency, two-phase commit | `compilation-dependencies.cc:887-913` | `[:world sym id]` guard, `commit!` rebase | **partial**: polled, not memoized; `commit!` (`world.clj:136-149`) has the right shape |
| Protector cells | `protectors.h:18-84` | aggregate cells (note D) | **missing** |
| Eager deopt with frame translation | `translation-opcode.h:16-42`; `deoptimizer.cc:839`, `:1009` | guard failure → resume T0 at the guard's position | **missing** (only replay from entry) |
| Lazy deopt (mark code, patch return addresses) | `deoptimizer.cc:245-290`, `:402` | not needed for world cells (M-D3) | **not needed** if M-P2's rule holds |
| Soft deopt, deopt poisoning | `globals.h:519-525`; `translated-state.cc:2110` | C §4.3 item 6 (15/100 budget, poisoning) | **design** |
| OSR at armed loop back edges | `interpreter-generator.cc:2187-2206`; `runtime-compiler.cc:296`; `bytecode-graph-builder.cc:905`; `osr-optimized-code-cache.h:26-27` | loop entry points into T1/T2 from T0 | **missing** |
| Concurrent compile, install on main thread at interrupt | `compiler.cc:376-404`; `optimizing-compile-dispatcher.cc:117-134`, `:202-225`; `stack-guard.h:51` | specialization as a pure job; CAS install | **partial**: install is a `swap!` (`stage.clj:141`); no jobs |
| Bytecode aging and flushing | `code.h:870-881`; `marking-visitor-inl.h:147`; `builtins-x64.cc:1241-1249`; `shared-function-info-inl.h:615-647` | cache eviction (free by R3) | **missing**; R6 not measured |
| Tiering by executed-work budget | `flag-definitions.h:601-624`; `interpreter-assembler.cc:1010`, `:1253`; `runtime-internal.cc:340-370`; `runtime-profiler.cc:188-232` | VOC planner, top level a fixed heuristic | **design** |
| Maps, transitions, deprecation and migration | `map.h:164-181`; `transitions.h:39-44`; `map-updater.cc:254-529` | logical shapes with schema versions (`01-core-v2.md:211`) | **design**; R7 |

Three facts behind the rows matter for the primitives. *Tiering* runs on
executed bytecode weight, charged on back edges and returns against a
budget stored in the `FeedbackCell` (`interpreter-assembler.cc:1020-1023`);
TurboFan fires at `ticks ≥ 3 + length/1100`, or early for small functions
if no IC changed since the last tick (`runtime-profiler.cc:198-208`). The
top policy is a fixed crude heuristic, as ladder principle 3 prescribes;
no expected-savings model exists in the tree. *Concurrent compilation*
splits a job into Prepare (main thread), Execute (background, reading the
heap only through a snapshotting broker, `js-heap-broker.h:128`) and
Finalize (main thread, after an `INSTALL_CODE` interrupt), where every
dependency is re-validated before install (`compiler.cc:376-404`,
`optimizing-compile-dispatcher.cc:134`, `:202-225`, `pipeline.cc:3764-
3767`). *Flushing* ages every bytecode array at each GC marking pass
(`marking-visitor-inl.h:147`); interpreter entry resets age and OSR
arming in one 16-bit store (`builtins-x64.cc:1241-1249`); old bytecode is
dropped and the function recompiles lazily
(`shared-function-info-inl.h:615-647`).

## 3. Required primitives

Klara today has: code values with hygiene and scope-extrusion checks,
`run` under the current basis, `genlet`/`with-genletrec`, the trivial
`specialize`, a cache keyed by (CodeId, assumption set), entry guards, and
certificate-checked install. A V8-class JIT needs seven more things. Each
is specified as data plus operations, so that the specializer and its
policies remain Klara code.

**M-P1. Sites and feedback as evidence values.**
- A *site* is `[code-id path]`, where `path` addresses a node of the K0
  term. CodeId, not closure, is the key, as V8 keys by closure-literal
  site through `FeedbackCell`: all closures of one `fn` form share
  feedback, and feedback survives a redefinition whose CodeId is unchanged.
- A *feedback value* is an element of a join-semilattice per site kind:
  `:call` (targets, by CodeId, cap k = 4, then `:mega`), `:arg-shape`
  (shape lattice of note J, cap 4), `:branch` (taken counts, saturating),
  `:arith` (long / double / overflowed / bignum, monotone). Join is the
  only update; every chain is finite (progress-or-saturate).
- Each site also holds a `:poison` set of guards that have failed there
  (V8's `kDisallowSpeculation`, `globals.h:1673`).
- `(feedback site)` is a stage-0 operation: it may be called while
  generating code, never from generated code. Its result has grade A with
  an argument-guard pseudo-cell (C §4.1), so using it forces a guard.
- Feedback lives outside the world, like the cache: deleting it changes no
  result (R3). In a fork it is read from the parent snapshot plus a local
  overlay and joined back on adoption. It is *selection* evidence under
  the held-out discipline (`architecture.md` §9, decision 5): a receipt may
  not claim a speedup measured on the runs whose feedback chose the plan.
- Collection: T1 code calls `(observe! site v)` at instrumented sites;
  T0 does the same through its entry hook. Lazy allocation as in V8
  (`flag-definitions.h:615-624`): a CodeId gets a feedback table only
  after its first budget exhaustion.

**M-P2. Assumptions with memoized validity on roots.**
- An assumption is `[:cell sym aspect hash]`, where `aspect` is
  `:value`, `:summary` (shape/effect summary, for early cutoff) or
  `:absent`, plus `[:shape id version]` and `[:protector id]` for
  aggregate cells.
- Rule: **assumptions are taken only on world cells, shape versions and
  immutable data**, never on atoms or mutable host objects. Facts about
  those are runtime guards. This rule is what makes M-D3 hold.
- An executable records `:root0`, the root it was specialized against.
  Validity for a root r is `(every? #(holds? r %) assumptions)`. Entry
  compares the fiber's basis with the executable's last validated root by
  identity (one load and compare). On a mismatch it revalidates once and
  memoizes `(exe, r) → bool` in a small weak table. Revalidation can be
  made O(changed cells) by consulting the change log between two roots,
  which `put-entry` already maintains as versions (`world.clj:95-110`).
- Publication does no work for executables (R1 holds by construction).
  The cost moves to the first entry under a new root, once per entered
  executable.
- Install uses `commit!`'s logic (`world.clj:136-149`): a specialization
  computed against b is installed for the current root iff its reads hold
  there; otherwise it is installed for b only, where pinned fibers still
  use it. V8's re-validation at commit becomes a lookup.

**M-P3. Deopt points and frame states in code values.**
- A staging form `(speculate guard fast slow)`, used inside `code`:
  `guard` is a runtime predicate, `fast` the code under it, and `slow` is
  *not* code but a resume point that the specializer fills in.
- Every speculation point in a K2 code value carries
  `{:id n :pos [code-id path] :env {binder → slot} :kont [frame …]
  :reason kw :kind #{:eager :soft}}`. `slot` is a residual local, a
  literal, or `[:captured shape fields]` for an allocation the specializer
  removed. `:kont` lists the frames of inlined callers and of handler
  frames erased by dispatch erasure (`01-core-v2.md` §4 item 2); it plays
  the role of `BUILTIN_CONTINUATION_FRAME`.
- On failure, generated code calls `(deopt! id live-values)`. The runtime
  builds the T0 machine state (term position, environment, continuation)
  from the frame state and continues in T0. Because T0's continuation is
  data, materialization is constructing a value. No stack walking or
  return-address patching is needed, so it is portable to every host.
- Effects already performed before the guard are not repeated, because
  execution resumes at the guard, not at entry. This replaces "replay from
  region entry" in the guarded-specialization square (`architecture.md:368-
  375`) with resume, and lifts the restriction to effect-free regions.
- `deopt!` joins the observed value into the site's feedback and adds the
  failed guard to `:poison` (`translated-state.cc:2110`). `:soft`
  (insufficient feedback) does not count against the budget
  (`globals.h:519-525`).
- Obligation: the frame state is *exact*. The specializer must keep every
  value the T0 state needs live, which is a liveness constraint on code
  generation that `esc`/`genlet` do not express today.

**M-P4. OSR entry points.**
- A K2/K3 code value may export entry points `{[code-id loop-path]
  (fn [env] …)}`, each taking the T0 environment of a `loop` (bindings
  and captured locals) and returning the loop's value.
- T0 counts back edges per loop site against the budget. When a loop
  is armed and an entry exists for the current basis, T0 calls it and
  passes the result to its own continuation. This is simpler than V8's
  frame rewriting (`bytecode-graph-builder.cc:905`, `OsrHelper`), because
  the T0 frame is a value and the compiled loop returns to it.
- OSR-exit is M-P3 at a loop header. An explicit basis raise at a back
  edge, for a long simulation that opts in to hot fixes, is OSR-exit, then
  `raise-basis!`, then OSR-entry into code valid for the new root.

**M-P5. Specialization jobs with atomic install.**
- `(specialize-job code-id root feedback-snapshot policy budget)` is a pure
  function. It may run on any fiber or thread because roots and feedback
  snapshots are values: V8's heap broker (`js-heap-broker.h:128`) is
  unnecessary for world data.
- Install is a CAS on the cache (already `swap!`, `stage.clj:141`) plus
  M-P2's validity rule. No main-thread interrupt is needed: a running
  generic frame keeps running, and the next entry sees the new
  executable.
- Jobs are cancellable, deduplicated by (code-id, assumption set),
  budgeted in time, and their certificate checks (ansatz) run in the same
  job.
- A deterministic mode runs jobs synchronously at fixed points
  (V8's `--predictable` turns off concurrent recompilation,
  `flag-definitions.h:2167`), so transcripts and experiments can
  reproduce tier choices.

**M-P6. Aging and eviction.**
- Each executable and each feedback table has an age. A sweeper (on a
  timer or after N publications) increments ages; entry resets them, as
  the trampoline does (`builtins-x64.cc:1241-1249`). Entries above a
  threshold are evicted. Eviction is always correct (R3).
- Executables valid only for roots that no fiber or fork pins are
  evictable regardless of age (weak references from executables to
  roots). This is the precondition for R6.
- On the JVM, executables are hidden classes so that one can be unloaded
  on its own.
- Never disable eviction globally: V8's LiveEdit turns off bytecode
  flushing for the isolate's lifetime after one patch
  (`liveedit.cc:1040`). That is exactly the R6 failure.

**M-P7. Bounded polymorphism in the cache.** The cache scans every
candidate for a CodeId (`stage.clj:159`). Cap the candidates at 4 per
(CodeId, basis). The fifth distinct assumption set marks the CodeId
`:mega`: it is specialized only on its S-graded inputs, with no argument
guards, and the budget of C §4.3 item 6 applies. This is R5's "churning
sites go generic".

**Costs.**
- *Feedback collection.* V8 pays for it in Ignition and in Sparkplug,
  which calls the same IC builtins, and limits it by allocating feedback
  lazily. On the JVM each `observe!` is a load, a compare and an
  occasional store, on top of HotSpot's own tier-3 profiling of the same
  bytecode. Budget: T1 with probes within 10 % of T1 without, so that
  feedback cannot by itself break R2. Unmeasured.
- *Deopt loops.* V8 has no general cap (`flag-definitions.h:917`,
  `reuse_opt_code_count = 0`) and relies on feedback monotonicity plus
  poisoning; its source still contains admitted loops (studies/v8.md §3).
  Klara should combine monotone feedback (M-P1), poisoning (M-P3), soft
  deopts, and C's 15/100 cap. Termination then follows from finite
  lattice height per site times the number of sites: a checkable bound,
  where V8 has a maintenance discipline.
- *Memory.* V8 keeps a `DeoptimizationData` per optimized code object:
  three words per deopt point plus the translation bytes, literals,
  inlining positions (`code.h:983-1008`). Klara's frame states are
  persistent maps and will be larger unless they share structure with the
  K0 term (positions are paths, not copies). Feedback tables are
  per-CodeId and must age (M-P6).

## 4. REPL interaction

**V8.** Live code change is a debugger feature. `LiveEdit::PatchScript`
(`liveedit.cc:975`) re-parses the whole script, diffs function literals,
and refuses if any changed function is on the stack
(`BLOCKED_BY_ACTIVE_FUNCTION`, `:922-924`) or is a suspended generator
(`:925-927`). If the patch goes ahead, it removes compilation-cache
entries, deoptimizes every affected function (`:1050-1051`, `:1113`),
gives the patched closures fresh feedback cells (`:1076`, `:1119`) and
disables bytecode flushing for good (`:1040`). Breakpoints deoptimize
(`Debug::DeoptimizeFunction`, `debug.cc:1371`); a break at function entry
deoptimizes everything in case the function was inlined anywhere
(`:1413-1416`). Side-effect-free evaluation is a separate
interpreter mode with a bytecode whitelist (`debug-evaluate.cc:424`,
`:993`; `debug.cc:2509`). The compilation cache is turned off while a
debugger is attached (`compilation-cache.h:205-209`). In short, V8 treats
an edit as an exceptional event that throws away optimization.

**Klara.** An edit is an ordinary publication. Against each gate:

- **R1** (publication independent of specialization count and fanout).
  Rules out V8's eager kill of dependent code. M-P2 satisfies it; the
  current per-entry polling also does, but at a cost on every call.
- **R2** (first correct result within max(5 ms, 10 %) of Clojure at p99).
  Specialization is never on the critical path (`01-core-v2.md:158`).
  T1 must be cheap, and feedback probes are charged against the 10 %.
- **R3** (deleting caches preserves results and effect traces). Requires
  feedback and caches outside the world, exact frame states (M-P3), and
  resume instead of replay.
- **R4** (old and new versions coexist). Executables are valid per root,
  not "current", so a fiber on the old root keeps its fast code. V8 cannot
  express this: a patched function's old optimized code is gone for
  everyone.
- **R5** (bounded cache cost). M-P7 and the deopt budget.
- **R6** (memory plateaus after 10,000 edits). M-P6, weak references to
  roots, and no global disable switch.
- **R7** (shape continuity without restart). This is V8's map deprecation
  with lazy instance migration (`map-updater.cc:254-529`, the
  `InstanceMigrationFailed` deopt reason). Klara's shape versions are
  world cells, so code depending on a layout takes a `[:shape id version]`
  assumption, and migration is an explicit world operation, not a side
  effect of a store.
- **R8** (expansion honesty). Its specialization analogue is O2 of note C:
  every fact a residual relies on is registered. I propose naming it
  explicitly, as R8′ "specialization honesty".

What V8 does that Klara should copy: fresh feedback for *changed* code
(Klara gets this for free, because a changed CodeId has no feedback), and
side-effect-free evaluation as a handler mode (Klara can do this with a
dynamic handler that refuses `:host/call`, no separate interpreter).
What it should not copy: refusing edits to active functions, and making
the debugger turn off caches.

## 5. Tier recommendation

**JVM.** HotSpot is the optimizing tier. Klara's emitted bytecode is
profiled by C1, compiled by C2 with type-profile inlining, deoptimized and
OSR'd by HotSpot. Klara should supply only what HotSpot cannot see:

- **T0**: the CEK interpreter. HotSpot sees one megamorphic eval loop for
  all programs, so T0 gets no help from the host JIT. Hence:
- **T1** (Sparkplug analogue): per-CodeId bytecode, emitted at a low
  threshold, possibly at definition like Chez. Its main job is to give
  HotSpot one method per Klara function, so that HotSpot's profiles are not
  polluted by the interpreter. It carries `observe!` probes.
- **T2** (the Maglev slot): world-level speculation that HotSpot cannot do.
  Basis constants become direct calls and cross-definition inlining;
  handler contexts are erased; shapes turn into primitive layouts and
  unboxed interfaces. Guards are coarse: entry checks plus a few
  `speculate` points. Fine-grained type speculation (long vs double on one
  operation) is left to C2, which already does it from its own profile.
  Double speculation, where Klara and C2 both guard the same fact, is
  wasted.
- **T3**: certified kernels (S3 fusion, raster), where the gain comes from
  laws, not speculation.

A separate Maglev-like tier between T1 and T2 is not worth it on the JVM.
The gap V8 filled twice (Turboprop, then Maglev) is the gap between
Sparkplug and an expensive speculative optimizer; on the JVM, C1/C2 fill
it. Klara's T2 already sits where Maglev sits: cheap, feedback-driven,
guard-based. T3 is expensive for a different reason (certificate checking)
and is scheduled by value of computation, not by hotness alone.

On the JVM, M-P3 is needed mainly for `speculate` points in T2 and for
T1/T2 → T0 exits. M-P4 is needed for T0 → T1 in long-running loops, which
matter for simulation. HotSpot's own deopt and OSR cover everything below.

**Chez (native).** Chez compiles every form fast and does no speculation
(`architecture.md:137`). T0/T1 collapse into Chez-compiled generic code.
T2 is Chez-compiled specialized code, and Klara must supply *all* of
speculation, deopt and OSR, because nothing underneath will. M-P3's
portable design (call `deopt!` with live values, resume in T0, no stack
patching) matters most here, as does M-P4's call-based OSR. A mid tier is
again unnecessary: Chez's compile cost for T2 is close to T1's, so there is
no expensive top tier to bridge, apart from T3.

**Recommendation.** Build M-P2 and M-P7 first, because they fix the
current per-entry cost and the unbounded cache and are host-independent.
Then T1 with M-P1 probes on the JVM, then M-P3 and M-P4 together, because
OSR-exit is deopt at a loop header. Defer M-P5 until jobs measurably block
interaction, and M-P6 until the R6 experiment runs.

## 6. Obligations and falsifiers

| # | Claim | Status | Falsifier |
|---|---|---|---|
| M1 | No lazy deopt (stack patching) is needed if assumptions are restricted to world cells, shape versions and immutable data | **Conj** | a needed optimization whose validity depends on mutable state that can change during a running activation, and which cannot be expressed as a runtime guard at a `speculate` point |
| M2 | Validity memoized per (executable, root) satisfies R1 and costs at most one identity compare per entry in steady state | **Conj** | a REPL workload where revalidation after publications costs more than the current per-entry polling (measure on 10,000 edits) |
| M3 | Frame states make deopt exact: resume at the guard yields the same observations and effect trace as the generic run | **Open** (generalizes O2) | a differential run where `deopt!` resumes with a wrong environment or repeats or drops an effect; check by deopting at every point (a stress mode like V8's `deopt_every_n_times`, `flag-definitions.h:783`) |
| M4 | Deopt cycles terminate within height(lattice) × sites plus the 15/100 cap | **Conj** | a workload that oscillates between two executables without growing any site's feedback |
| M5 | On the JVM, T2 speculation on facts C2 also profiles brings no gain | **Conj** | a benchmark where a Klara arith guard beats C2's profile-driven code by more than noise |
| M6 | A Maglev-like tier between T1 and T2 is not needed on the JVM or on Chez | **Conj** | T2 compile latency that blocks R2 or leaves hot code in T1 for more than a stated fraction of run time |
| M7 | Feedback probes in T1 cost within 10 % of unprobed T1 | **Open** | measurement |
| M8 | Feedback keyed by CodeId, shared across forks with join on adoption, never changes a result | **Conj** (R3) | any program whose output differs with feedback cleared, or between forks with different feedback |
| M9 | Memory plateaus with M-P6 (R6) | **Open** | heap growth across 10,000 edits with fibers released |

## 7. Questions for Christian

1. **Restriction M1.** Do you accept that the specializer may not take
   assumptions on atoms or host-mutable state, only runtime guards? It
   removes lazy deopt entirely, but it means a hot loop over an atom's
   contents gets no cell-level folding.
2. **Feedback in forks.** Is feedback an authority (split at fork, like
   evidence in RFC 0001) or shared data with join on adoption? I propose
   the latter, since it never changes meaning; the evidence discipline
   then applies only to receipts.
3. **Ladder change.** Split level 3 into 3a (inline feedback, ns, always
   on in T1) and 3b (sampled measurement)?
4. **Replay vs resume.** May the guarded-specialization square in
   `architecture.md` §8 change from "generic from entry (replay)" to
   "generic from the guard (resume)" once M-P3 exists, keeping replay as
   the fallback behind opaque host frames?
5. **T1 at definition time** on the JVM (Chez-style), or at a first
   budget exhaustion (Sparkplug-style)? It depends on bytecode emission
   plus hidden-class load latency, which is unmeasured; R2 decides.
6. **V8 checkout.** Should `../v8` be updated so that Maglev, Turboshaft
   and the tiering manager can be cited from source? The note's
   conclusions about the JVM do not depend on them; the Chez tier design
   might.
