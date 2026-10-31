# Runtime alternatives after the private-state and activation experiments

Review date: 2026-10-29. This is a proposed decision sequence, not a new runtime
or a claim of measured performance. No sibling repository or production source
was changed for this review. Source inspection, rather than builds of the three
external runtimes, supplies the comparisons below.

## Decision

Keep fused T0 as the full-language implementation and semantic recovery target.
Keep prepared nodes as the experimental baseline; the boxed activation kernel
has not earned promotion. Stop expanding both experimental kernels in parallel.
Spend the next bounded performance effort on **removing repeated generic
loop/call machinery and guest dispatch**, comparing minimal generic emission
with existing checked primitive emission before introducing a new backend.
Typed storage is a secondary controlled hypothesis, not the presumed cause of
the remaining gap. Spend the corresponding semantic effort on one useful mixed execution
boundary, not another complete interpreter.

CEK is a description of control, environment and pending work. It does not
require map-shaped states, linked continuation cells, tree walking, boxing, or
one dispatch per semantic transition. An AST evaluator, register interpreter,
stack interpreter and generated body can all implement that semantics. Conversely,
a register machine does not supply correct effect handlers or continuation
recovery merely by possessing a program counter. The bridge and the execution
kernel answer different questions.

The current [runtime contracts](../../doc/engineering/runtime.md)
remains useful for ownership and recovery contracts. Read its activation-program
recommendation conditionally: the subsequent experiment failed its promotion
gate. A common runtime contract does not require a permanent proliferation of
physical engines, adapter layers or compiler IRs.

## What the measurements actually establish

The [private-state experiment](MEMORY.md) reduced allocation sharply and improved
several larger pure workloads by roughly 4.4–5.4 times against its contemporaneous
fused T0. Its 10,000-iteration scalar sum still took roughly 2 ms, compared with
about 3 microseconds for compiled Clojure. That gap is too large to address by
frame packing alone. Vector updates were much closer in allocation, because
persistent result construction remains real guest work.

The [activation comparison](ACTIVATION.md) gained roughly 22–34% on several
larger families but lost on small calls, including an approximately 18% loss
under extended warmup. Recovery also became more expensive through its current
adapter. Flattening control is therefore promising for some workloads but is
not a demonstrated general runtime improvement. Neither experiment covers
ordinary globals, arbitrary host interaction, effects, staging or managed
mutable application state. Retained heap and GC remain unmeasured.

Historical T0/SCI/Clojure ratios concern an older cohort and different warmup.
They cannot be multiplied by later speedups or used as current SCI comparisons.
A useful next report must contain current end-to-end calls, not just warmed
kernel throughput.

## Current SCI evidence changes the next experiment

The subsequent [Chez experiment](CHEZ-EMPIRICAL.md) measures a working native
compiler. The [bounded refinement experiment](REFINEMENT.md) supplies initial
source-specific slot-block proofs and additional snapshot/failure checks.

The newer [current-tier cohort](../baseline/CURRENT.md) compares the current
engines with published SCI 0.15.59 under a common harness. One process at
n=10,000 measured scalar summation at approximately 121 microseconds and
477 KB for SCI, 2.00 milliseconds and 483 KB for private nodes, and
1.53 milliseconds and 481 KB for activation programs. These illustrative
numbers are from process 0; the linked report owns the complete cohort and
its aggregation. Similar allocation with a roughly 16-fold node/SCI time gap
means boxing/allocation volume alone cannot explain the gap. The shape of
execution, calls, guards and host-JIT opportunities deserves attention before
assuming primitive arrays are the next best intervention. Equal allocated
bytes does not establish identical allocation sites or GC behavior.

Source inspection identifies a concrete difference. Both the local SCI checkout
(`0d38f0c95338cbf03c82d96ab5943ab07821d4f4`) and the source embedded in the
published 0.15.59 jar lower `loop*` into a let plus an immediate function call.
It would therefore be inaccurate to claim SCI simply has a dedicated loop AST.
However, SCI's `return-recur` emits specialized nodes which evaluate all recur
arguments using old bindings, write the resulting values to invocation-array
slots and return a recur sentinel. Its generated function wrapper handles that
sentinel in a host `loop`, reusing the invocation array. Captured-environment
copying and ordinary function entry happen outside that loop. See local
`src/sci/impl/analyzer.cljc:280` and `:971`, and `src/sci/impl/fns.cljc:175`;
in the published jar the corresponding locations include analyzer lines 287/921
and fns lines 54/79. The local fork additionally has world/context machinery;
its performance was not measured by this published-artifact cohort.

Klara's `src/klara/expand.clj:448` lowers `loop*` to `letrec` plus application.
In `mutable.clj:169`, each completed application still validates the closure
and arity, decides slot reuse and copies the capture prefix before entering the
body. `activation.clj:137` likewise handles a generic tail call, including
layout/reuse decisions and argument/capture copying; reuse clears slots.
Specializing a statically established self-tail transfer could avoid much of
this work without eliminating boxing. This is a source-supported hypothesis,
not a profile proving the complete cause of the measured gap. SCI's ordinary
node evaluation and host compilation differ as well.

SCI is a structural and performance precedent, not a proposed Klara substitute.
The local SCI already supports forkable contexts; that is separate from this
published benchmark and does not establish Klara-equivalent control, authority
or staging semantics. This review makes no global claim about SCI continuation
support. Klara should derive execution from its own reference model and prove
small lowering/recovery obligations, rather than pick a runtime from a scalar
benchmark.

## What the sibling runtimes do, and what transfers

The inspected revisions were:

| Checkout | Revision |
|---|---|
| Graal | `d2e7bd1e957d593e614d240311c4b7a78d983e82` |
| Valhalla JDK | `775bcc5bdf2a085bc06c1c38102aa79e71f35ae0` |
| V8 | `5fe0aa3bc79c0a9d3ad546b79211f07105f09585` |

Paths below are relative to those checkout roots. These are source observations,
not assertions about a future release or the active installed JVM.

**HotSpot/Valhalla.** In
`src/hotspot/cpu/x86/interp_masm_x86.cpp:744`, `dispatch_base` emits a safepoint
poll and an indirect machine jump through a dispatch table. This is generated
native interpreter machinery, not Java source calling a function pointer.
HotSpot already supplies JIT compilation and GC for Klara's host methods;
Klara can reuse those facilities by emitting ordinary JVM methods. It cannot
ask HotSpot to treat an arbitrary guest `Object[]` instruction stream as JVM
bytecode, or use HotSpot's internal deoptimizer as a guest continuation API.
`src/hotspot/share/runtime/deoptimization.cpp` separately reallocates eliminated
objects and reassigns their fields: recovering optimized state is substantial
machinery even when the VM owns the entire stack and heap representation.

Valhalla's `src/hotspot/share/oops/inlineKlass.hpp:91` describes distinct flat
layouts with nullability and atomicity constraints. This is relevant to future
compact immutable records and arrays. It does not automatically unbox arbitrary
Clojure numbers in `Object[]`, remove an interpreter's dispatch, implement
persistent application state, or make a mutable frame independently forkable.
Do not require a Valhalla toolchain for this work. Primitive Java arrays already
allow the central typed-storage experiment on the current runtime. A future
value-record layout comparison is meaningful only after a supported toolchain
and a measured retained-object problem exist.

**V8.** `src/interpreter/bytecodes.h` specifies register operands with an implicit
accumulator. `src/interpreter/interpreter-assembler.cc:1184` loads the next
bytecode and tail-dispatches to a handler entry. Those handlers are generated
machine code. A Java `IFn` or `MethodHandle` table is not equivalent: it retains
host calls and has no general guaranteed tail-jump semantics.
`src/baseline/baseline-compiler.cc:293` walks bytecodes and emits code with
position mapping; `VisitAdd` at line 980 calls a baseline builtin. This supports
a useful distinction: baseline compilation can remove dispatch without first
proving all arithmetic primitive. Later specialization can remove generic
operations. `src/deoptimizer/translated-state.cc` reconstructs object graphs
and tracks duplicate object identities. The transferable design is a shared
logical frame convention plus explicit recovery recipes. V8's native assembler,
GC object layouts, tagged values, runtime builtins and deoptimizer are not
components to drop into Klara's JVM execution path.

**Graal/Truffle.**
`truffle/src/com.oracle.truffle.api/src/com/oracle/truffle/api/impl/FrameWithoutBoxing.java`
uses parallel `Object[]`, `long[]` and tag arrays. Its `materialize()` returns
`this`; materialization there does not create a separate frozen snapshot.
`truffle/docs/bytecode_dsl/BytecodeDSL.md` explicitly distinguishes improved
interpreter execution, quickening, boxing avoidance and guest compilation.
`truffle/docs/HostCompilation.md` distinguishes compiling interpreter Java code
from partially evaluating the interpreter against a guest program, and describes
special compiler support for annotated interpreter switches. Ordinary HotSpot
compilation of Klara's dispatch loop does not imply the guest program becomes
constant and dispatch disappears. Useful lessons are typed lanes, bounded
specialization, cold/hot preparation policies and explicit materialization.
The Bytecode DSL and its partial evaluator are not reusable without adopting
their runtime/compiler contracts. This proposal adds no Truffle dependency.

No source is copied from these projects. Any later source reuse would require
license review independently of whether the design idea is applicable.

## Alternatives ranked by the question they answer

| Option | What it can improve | Cost and decision |
|---|---|---|
| Prepared nodes with private storage | Administrative allocation and repeated Core decoding | Existing experimental baseline; preserve until an alternative wins full calls |
| Packed register/accumulator bytecode | Instruction footprint, fewer dispatches, direct local access | Activation experiment is related evidence, not a test of every packed layout; at most one bounded encoding comparison after a profile identifies decode/cache cost |
| Stack bytecode | Simple emission and compact operands | More stack traffic/dispatch may offset density; no reason to implement a third full engine now |
| Direct threaded native interpreter | Dispatch branches and handler calling convention | Requires native code generation or a native runtime; not available as a portable Java switch trick; defer |
| Java dispatch/storage kernel | Remove host reflection, generic invocation or awkward Clojure compilation | Port only a measured inner kernel with the same admission and bridge, not the language |
| Typed lanes and guarded quickening | Boxing and generic numeric calls within interpreted execution | Secondary hypothesis after loop/call structure; still pays guest dispatch and tag/guard costs |
| Baseline JVM method emission | Remove guest dispatch while retaining generic operations where needed | Reuse current emitter first; explicit resumable boundaries needed for general effects |
| Typed checked JVM regions | Remove dispatch and per-iteration boxing together | Highest priority for scalar peak performance; existing compiler provides a starting point |
| Partial evaluation of a whole interpreter | Potentially derive guest code from execution semantics | Needs stable program specialization, effects, termination bounds and recovery; do not build a new PE framework now |
| Tracing hot guest paths | Specialize observed paths and loops | Recording, side exits, polymorphic trace growth and invalidation are a new compiler project; defer until structured compilation misses valuable hot paths |
| Direct machine-code emission | Full control of registers, ABI and native dispatch | GC roots, safepoints, executable memory, unwind/recovery and portability make this much larger; no current evidence justifies it |

Register versus stack is not a language architecture decision. Keep source
positions, closure identity and recovery descriptions independent of the
instruction encoding, but avoid making an extensible backend framework for
hypothetical encodings. An experiment may use the current small kernel op map;
production should have one selected baseline plus compiled regions.

## The most decisive next performance comparison

Use a fixed admitted fragment and compare three paths:

1. Current prepared nodes, preserving a simple baseline and recovery model.
2. Minimal generic JVM/Clojure-form emission using the existing emitter where
   possible: retain boxed arithmetic helpers, but emit actual host control flow
   and self-tail `recur`. This isolates the value of eliminating guest dispatch
   and repeated generic call entry before crediting primitive arithmetic.
3. Existing checked primitive emission of the same program, including admission,
   errors and full call overhead. This measures the additional value of typing.

Include a loop, a closure-heavy small call and a generic arithmetic/type-changing
case. Do not create another compiler IR for this comparison. If minimal generic
emission cannot be expressed with the existing lowering without large changes,
a bounded recognized self-tail backedge in the node engine is an alternative
probe, not an additional permanent tier. Prove target/layout stability, evaluate
all arguments before overwriting slots, retain captures and observable scopes,
and preserve a reconstructible state at supported boundaries.

Primitive-lane nodes remain a useful later controlled comparison if interpreted
execution still dominates a valuable workload. Use `long[]`/`double[]` plus
reference storage and tags, or exact bit conversion in one primitive array.
A small Java helper is justified only if bytecode inspection demonstrates that
the Clojure loop cannot express the desired operations cleanly. Compare the same
layout and operations so a gain can actually be attributed to Java.

Begin with exact Long addition/comparison and self-tail loops. Exercise
out-of-cache numbers, overflow, type changes, mixed numeric input, cold calls
and inputs that decline admission. Add Double only with raw-bit, NaN, signed
zero and error-order tests. BigDecimal and ratios remain generic, with the
existing math-context contract. Store the already-computed operands before
fallback; never replay a primitive or prior effect to obtain them again.
A specialized slot must box the exact logical value on recovery. Dropping
reference entries is allowed only when it preserves required authority
reachability; numerical liveness does not authorize general capture trimming.

Quickening should be a small guarded side table keyed by prepared program and
site, with a bounded generic fallback after unstable types. It must guard the
primitive identity and every world/context assumption used by the operation.
A shared profile may suggest an optimization; it cannot authorize that operation
in a different world. Measure the tag checks and specialization churn. Do not
assume typed arrays outperform optimized boxed locals on tiny calls.

`src/klara/compile/emit.clj` already emits Clojure forms with self-tail `recur`,
primitive lanes and restricted deopt points; `compile/pe.clj` already performs
bounded K1 simplification. First make their admitted scalar path concrete and
measure its unsupported cases. A generic emitted JVM body is a sensible next
baseline hypothesis if it materially expands coverage at low compilation cost.
Direct JVM-bytecode emission should replace Clojure-form emission only after
inspection identifies a blocking artifact: unwanted boxing, excessive adapter
calls, unavailable primitive signatures, compilation latency or code size.
It avoids dependence on Clojure's compiler choices but introduces verification,
stack-map, class unloading and maintenance costs. It is not native emission;
the JVM still chooses machine code and optimization policy.

## Full semantics and persistent worlds are the architecture

A fast pure kernel is useful, but is not yet a replacement runtime. Use the
existing Core and T0 observations to establish the following shared contract,
rather than teaching each engine its own world/authority system:

- A code basis and closure mint basis determine definition identity. Open
  closures and global changes need explicit lookup/guard behavior.
- An active managed-state root, if introduced, resolves stable managed reference
  identities. Ordinary host atoms are currently shared and do not become
  persistent by freezing execution arrays.
- Rights, continuation shot counts, loans, cancellation and settlement retain
  live lifecycle identity. They cannot be rolled back by restoring an old image.
- An execution lease owns working arrays and installs declared host context,
  including decimal math context. Reentrant callbacks use separate ownership
  while preserving the required dynamic and code context.

These distinctions need not become four elaborate class hierarchies. They are
four different invariants that a small explicit execution context must preserve.
Stable logical closures should eventually be callable by either execution tier;
the present private/T0 closure conversion is a restricted bridge, not a reason
to maintain two permanent guest value systems.

Expand boundaries in dependency order. First pin down globals/open closures,
rest arguments, errors and one host callback path. Unsupported code declines
before execution. Next support one genuine post-effect recovery point that
reconstructs pending operands and resumes exactly once. Then address delimited
capture, deep handler reinstatement, cleanup, repeated shots and rights reached
after capture. Preserve the current unused-capture rejection until a deliberate
semantic change is approved. Arbitrary JVM frames cannot be cloned to implement
multi-shot guest continuations; generated bodies must expose supported
suspension points or transfer to the explicit machine before those operations.

Keep build/staging execution in T0 initially. Let-insertion loci and their atoms
need their own alias/ownership treatment. A private ordinary runtime should
nevertheless have a precise transfer boundary for `code`/`run`, with levels,
world bases and source identities intact. This makes staging compatible with
faster execution without making a full staged compiler heap a prerequisite.
A later persistent compiler-job workload can decide whether build snapshots
are worth implementing.

For application-state forks, define managed references and branch visibility
before implementing CoW. Immutable roots plus branch-local writes are a
reasonable starting point. Host calls need declared read/write/callback contracts;
intercepting explicit host syntax does not classify transitive mutation.
Control capture, state snapshot and authority split remain separate operations.
Failure after a partially prepared fork must settle reservations, not publish a
half-authorized branch. Merge requires a policy for each state kind; a dictionary
union cannot merge definitions, ordinary cells, evidence and linear rights alike.

Copying execution snapshots remains the audit baseline. Test retained memory
with long-lived closures, many paused branches and a large discarded activation.
Only then compare segmented immutable chunks/CoW, including write barriers and
release costs. Faster capture that retains whole obsolete worlds may be a net
regression. Bound prepared/native caches and pools; clear dead buffers where
semantically valid. Durable process snapshots and arbitrary host-heap cloning
are separate projects.

## Derive the optimization from a small semantic obligation

The reference CEK gives a starting specification, not a performance mandate.
For a self-tail backedge, define a relation between private slots/program position
and the existing Core environment/pending continuation. Show that the optimized
transfer corresponds to the original application steps: same evaluated callee,
left-to-right arguments, arity/error behavior, capture bindings and continuation.
Administrative steps may disappear; effects, errors and authority observations
may not. A statically recognized source `recur` label alone is insufficient if
intervening lowering or control scopes alter these conditions.

For emitted bodies, first restrict to code admitted before execution. Specify
entry assumptions and each recovery point; validate reconstructed values,
aliases, context and next operation against reachable reference states. Prove
or mechanically check each small lowering rule where feasible, then compose
under explicit assumptions. Differential pause/resume tests and numeric edge
cases supply empirical evidence while those proofs remain incomplete. Do not
call existing bridge tests a whole-language correctness theorem.

Only after that pure relation is stable extend it to one effectful boundary,
including exactly-once execution and live authority identity. This is a
first-principles path toward a coherent model: semantic relation first, bounded
implementation second, performance admission third. It does not require proving
an entire new interpreter before learning whether its cost structure is useful.

## A bounded sequence with stop conditions

The following are proposed engineering budgets and decision targets, not
measured promises. Limit each experiment by scope before considering extensions.

| Step | Deliverable and suggested effort cap | Decision target |
|---|---|---|
| 1. Establish a useful workload | 1–2 engineering days: current full-call baseline for a small data transform, closure-heavy evaluator task, and a handler/fork workflow; include preparation, fallback frequency and retained-heap scenario | Select one workload whose user-visible cost is actually dominated by Klara execution; otherwise optimize its dominant boundary first |
| 2. Separate loop/control overhead from numeric overhead | 3–5 days: nodes versus minimal generic emission versus existing checked primitive emission, same source/input and correctness checks | Generic emission: seek at least 2× full-call loop improvement across three processes with no unexplained >10% small-call regression; checked scalar loop: investigate a target within 3× compiled Clojure full-call time at n=10,000 and constant arithmetic allocation; report preparation and declining cases separately |
| 3. Remove the largest measured integration obstacle | 3–5 days: one of direct recovery, selective Java kernel, or emitter adaptation—not all three | At least 20% full-call improvement on the chosen useful workload, with compilation/preparation break-even inside its measured reuse count; otherwise retain simpler path |
| 4. Establish one full-language boundary | 5–10 days: chosen real workload crosses a declared host/global/effect boundary and resumes without replay; include failure injection and both T0 drivers | Exact observations, aliases, authority/lifecycle identity and error ordering; no performance waiver for mismatch |
| 5. Choose production subset | Review after steps 1–4: one prepared baseline or compiler-only admission plus T0, retained-heap/cold-call report and explicit exclusions | Enable only a demonstrated subset with profitable full calls and bounded retention; delete or archive losing experimental code rather than expanding all engines |

The loop throughput target is deliberately stronger than another 20%
representation improvement: the scalar gap calls for a different cost structure.
The compiled target is an investigation threshold, not a universal promise for
small, effectful or polymorphic programs. Failure is informative: identify
whether time is in entry guards, generic operations, boxing, dispatch or result
construction before changing the next component.

Use at least three independent JVM processes for decision measurements, with
paired ordering, sufficient warmup, raw samples and identities. Do not run
concurrent benchmark cohorts. Separate cold preparation, warm full invocation,
residual body, snapshot/recovery and retained-heap phases. Include a deliberate
losing input and a type/world invalidation case. Report break-even as measured
extra preparation cost divided by measured per-call saving only when the saving
is positive; include compilation and guard costs in the relevant alternatives.

The result should be fewer runtime mechanisms: one canonical semantic input,
one ownership/recovery contract, one selected ordinary execution baseline, and
checked emitted regions. None of the external runtimes supplies Klara's effect,
staging or world semantics. Their strongest lesson is to make the fast common
path cheap while retaining explicit metadata and ownership at the uncommon
boundaries that must reconstruct it.
