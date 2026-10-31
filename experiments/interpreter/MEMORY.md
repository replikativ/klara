# Private mutable CEK state

This is a representation experiment for a **closed pure Core fragment**, not
a replacement runtime or a managed-reference implementation. It tests whether
persistent logical worlds require persistent updates for interpreter working
state. They do not: the prototype keeps private working state in mutable arrays
and copies it explicitly when retaining a snapshot.

The default T0 driver remains unchanged by this probe. Truffle is not a
dependency. All implementation code in this probe is Clojure; `deftype` nodes,
JVM object arrays and `ArrayList` buffers provide compact representations.

## Representation and ownership

| State | Representation | Preservation rule |
|---|---|---|
| Code | Prepared immutable `Node` objects with numeric tags and direct fields | Shared between executions; no instruction rewriting |
| Current control/environment | Loop registers and an object array | Exclusive while `advance!` runs |
| Pending work | Reusable frame arrays and argument buffers | Slots reused only after popping the frame |
| Closure captures | Copied lexical prefixes; sealed recursive groups | Never mutated after construction completes |
| Tail-call locals | Reused working array when no active frame refers to it | Otherwise allocate a separate array |
| Retained state | Opaque in-memory `Frozen` snapshot | Copy active registers, environments and argument buffers |
| Resumed state | Fresh mutable buffers from `thaw` | Each resumed execution owns its buffers |

The interpreter still dispatches Core operations: code is predecoded, not
compiled into a JVM loop for the source program. Numeric operations retain
Clojure's checked generic arithmetic and boxed values. Data-vector updates
remain persistent; this experiment mutates interpreter internals, not guest
collections. It does not silently convert application vectors into arrays.

Input and quoted data are recursively checked before execution. Only exact
supported immutable scalars and ordinary persistent vectors are accepted.
The closed primitive family cannot introduce mutable host leaves into these
vectors, so operations need only check immediate value families. Function
identity is checked before a primitive executes. An overridden function
declines before calling it. The prototype has no arbitrary host calls,
global resolution, staging, handlers, rest arguments or guest mutable cells.
Internal closure calls, mutual recursion and non-tail recursion work; closure
values cannot escape through the public `invoke` result.

`advance!` requires exclusive access. Freeze only between advances, after the
owner stops changing buffers. This is not concurrent snapshotting or automatic
quiescence detection. Host code can access the low-level objects; opacity is an
API convention, not a sandbox. Exceptions make a private machine unsuitable for
further use; discard it. No authority rights, external effects or expenditure
ledger are snapshotted or duplicated.

Snapshot copying is proportional to active working state and buffer capacity.
It is not O(1), a durable image, or a copy-on-write implementation. Closure
captures and immutable guest values can be shared. Future page/chunk sharing
would need explicit ownership and preservation rules. Spindel-style live
overlay reads that track a changing parent are a distinct observation policy
from the frozen snapshots used here.

## Run and check

The [one-way T0 reconstruction bridge](BRIDGE.md) now adds a controller over
this pilot, retaining exact source nodes, explicit decimal context and transfer
leases. It remains a pure-fragment experiment; general effects and managed
references are not admitted. The check command includes its additional tests.

The snapshot guarantee concerns private working buffers, not complete host
context. The pilot admits BigDecimal arithmetic, which depends on Clojure's
`*math-context*`: the same frozen computation can return different results under
different precision bindings. The [host-context probe](dynamic_context_contract.clj)
demonstrates this. The recorded execution comparisons use a fixed host context.
A resumable runtime must capture an admitted context, guard compatibility or
restrict the operations it accepts; see the
[runtime contracts](../../doc/engineering/runtime.md).

```sh
clojure -M:memory-probe --check
clojure -M:memory-probe 0
clojure -M:memory-probe 1
clojure -M:memory-probe 2
clojure -M experiments/interpreter/mutable_summary.clj
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M experiments/interpreter/mutable_snapshots.clj
```

The original three private-state checks contain 208 assertions. They compare supported programs with
both T0 drivers, pause at multiple transition boundaries, resume the original
and several independent thaws, and exercise captured aliases, mutual/non-tail
recursion and larger environments. Rejections include host effects, handlers,
staging, mutable input leaves, escaping closures and changed primitive roots.
Checked arithmetic overflow is preserved. These tests do not prove a complete
simulation theorem or support the full Klara authority/handler semantics.
The probe's transition fuel differs from T0 and source-language step counts.
The bridge adds reachable-state and ownership checks; see its separate report
for the combined current test count.

## Recorded measurements

The [aggregate](results/mutable-summary.edn) and [table](results/mutable-summary.tsv)
retain three independent JVM reports. Each warms all engines with 40 calls and
collects nine samples of five calls with rotating order. Preparation is excluded;
machine construction, input/output admission and execution are included.
The T0 control is the current fused driver with compiler hooks disabled. Host
Clojure executes the same source forms. Sources, raw samples, preparation time
and JVM flags are retained. Hardware: Intel Core Ultra 7 258V, Linux x86_64;
JDK `25.0.1+8-LTS-jvmci-b01`, Clojure 1.12.4, JVMCI enabled, 1 GiB heap.

| Workload | Input | T0/private CEK time | Allocation reduction |
|---|---:|---:|---:|
| Summation | 10,000 iterations | 4.39–5.16× | 98.5–98.6% |
| Local calls | 10,000 iterations | 4.97–5.40× | 97.3% |
| Persistent vector updates | 10,000 iterations | 4.85–5.42× | 95.9% |
| Loop beneath a caller | 10,000 iterations | 4.39–4.75× | 98.5% |
| Small higher-order closure composition | One call | 1.59–1.78× | 76.1–76.6% |
| Non-tail Fibonacci | n = 16 | 2.47–2.68× | 97.3% |

Summation falls from 32–33 MB to about 479 KB per call. Persistent vector
updates fall from 85–86 MB to about 3.52 MB; Clojure's data updates allocate
about 3.28 MB on that workload. This is evidence that interpreter bookkeeping
allocation can be reduced substantially without mutating persistent guest data.
It is not an attribution of each representation change separately.

The remaining speed gap is substantial: private CEK summation takes about
1.95–2.15 ms versus 3.1–3.4 microseconds for compiled Clojure. Vector updates
take about 4.93–5.21 ms versus 0.34–0.50 ms. Dispatch and boxed arithmetic remain;
mutable storage alone does not yield machine-code loop performance. The probe
also has fewer capabilities and safety obligations than general T0. Its gains
cannot be extrapolated to handlers, arbitrary callbacks or whole applications.

A separate [snapshot measurement](results/mutable-snapshots.edn) freezes and
thaws one paused Fibonacci execution. Its median is about 5.49 microseconds and
4.64 KB per pair in one process. Execution after resumption is checked outside
timing. This is one active-state shape, not a general fork-cost estimate.
Snapshot costs are excluded from the execution table; an application that
snapshots frequently must account for them. Retained memory and GC costs have
not been isolated. Timing samples do not establish steady-state confidence
intervals or performance parity with another complete language runtime.

## What this suggests for Klara

Keep a simple reference evaluator and make execution representations selectable.
Define ownership and snapshot contracts before exposing mutable storage to guest
compiler code. A future optimized path must preserve world bases, handlers,
authority and deoptimization, or decline before executing unsupported behavior.
The pure-fragment admission used here is one bounded way to establish that
private mutation is unobservable; it is not the general solution.

The focused formal obligation is a relation from private buffers to logical
control, lexical environments and pending work. Private transitions must match
reference observations, freeze must preserve that relation, and separate thaws
must remain independent. Moving this implementation into Klara's affine subset
would additionally need the actual lowering/representation bridge checked.
Primitive loop emission remains necessary for peak numerical performance.
