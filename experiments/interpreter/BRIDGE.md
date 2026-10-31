# Private CEK to T0 reconstruction

This implements the first bounded reconstruction milestone from the
[runtime contracts](../../doc/engineering/runtime.md).
It is an experimental **one-way** bridge for the private interpreter's closed
pure fragment, not a production runtime switch or a complete refinement proof.

## Try it in a retained host REPL

Start once with experiment sources on the classpath:

```sh
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -r
```

```clojure
(require '[interpreter.bridge :as b]
         '[klara.expand :as x]
         '[klara.world :as w])

(def artifact
  (b/prepare
    (x/expand-expr '(fn [n] (+ 10 (* n 2) 3)) w/empty-root)))
(def call (b/start artifact [4]))
(b/advance! call 8)
;; => :paused
(def transferred (b/transfer! call))
(take 2 (:state transferred))
;; => (:ret 8)
(select-keys (first (nth (:state transferred) 3)) [:tag :vals :todo])
;; => {:tag :list, :vals [10], :todo ({:op :quote, :datum 3})}
(b/resume! transferred)
;; => 21
```

The multiplication and first argument have already been evaluated. The bridge
materializes their values and pending work; it does not regenerate a call from
the entry function. The private capsule is now `:transferred`. Advancing,
freezing or transferring it again declines. Resuming the transfer a second
time also declines. A snapshot explicitly creates independent pure alternatives:

```clojure
(def call (b/start artifact [4]))
(b/advance! call 5)
(def snapshot (b/freeze call))
(b/resume! (b/transfer! (b/thaw snapshot)))
;; => 21
(b/resume! (b/transfer! (b/thaw snapshot)) false)
;; => 21 ; use the ordinary fused T0 driver instead of drive-reference
```

These are controller API leases, not authority tokens or enforcement against
arbitrary host access. Raw machines and reconstructed states remain trusted
host interfaces. Calling `ev/drive` directly bypasses the controller's context
and lifecycle checks. The bridge is not a sandbox.

Ordinary completion can use `b/invoke` or `b/result!` without reconstructing
CEK state. The [activation comparison](ACTIVATION.md) exercises a second kernel
through the same controller. Transfer remains an explicit boundary operation.

## Representation relation

Preparation can optionally record an identity map from every private `Node`
to its exact original Core object. The bridge retains a read-only view of this
map, the source CodeId and an explicit pinned basis. It therefore preserves
Core metadata and scope indices instead of guessing source from node fields.
Ordinary private-interpreter preparation need not allocate this index.

At a quiescent pause, reconstruction converts:

| Private representation | Existing T0 representation |
|---|---|
| Eval/return registers | `[:eval term env k]` / `[:ret value env k]` |
| Active array prefix | Persistent `:locals` vector with declared `:basis`/`:mint` |
| Let/if frames | Existing map-shaped `:let`/`:if` frames |
| Operand cursor and value buffer | `:list` frame with evaluated `:vals` and remaining `:todo` |
| Private closure | T0 `Closure` over the exact Core function |
| Shared recursive capture array | Shared delayed persistent capture vector |
| Bottom-first private stack | Top-first persistent T0 continuation |

One identity memo maps private closures to T0 closures within a transfer.
Another memo ties recursive capture environments through promises. This
preserves closure aliases and recursive cycles, including shared environments
between mutually recursive functions. Full captured prefixes are retained;
no free-variable trimming or authority-envelope approximation is performed.
Working arrays and reusable argument buffers do not escape into T0 state.

This preserves graph identity relationships within one reconstructed state.
It does not establish a general host-object identity contract between separate
transfers, nor admit closures crossing the public input/output boundary. The
controller still accepts only the pilot's immutable data inputs/outputs.

## Context and lifecycle

This milestone supports closed entries under one explicitly pinned basis.
The mint basis is that same root. Open closures, arbitrary outer continuations,
mixed-world closure graphs and general managed state remain unsupported. The
tests inspect retained bases; they do not establish global lookup semantics
for the private tier, which still declines global references.

A new call records the caller's current immutable decimal `*math-context*`.
Each private advance and T0 resumption rebinds that setting. Freeze/thaw retains
it across host thread changes. A new call to the same prepared entry can use
a different setting. Initializers are evaluated once during preparation under
their then-current context; materialization retains their computed values.
This fixes the raw pilot's decimal-context counterexample for calls managed
by this controller. It is not blanket capture of arbitrary dynamic bindings.

Primitive identities are checked before preparation, execution and transfer.
Replacing an admitted primitive causes a decline before the replacement runs.
The contract excludes concurrent arbitrary host redefinition while T0 is
executing; it is not an isolation guarantee against outside host mutation.
Reference execution disables compiler hooks and starts without an inherited
host continuation or fiber. Compiled-entry integration is a later step.

The controller serializes operations on a capsule. Its states include paused,
advancing, done, returned, transferred and failed. Reconstruction completes before
ownership transfer, so a rejected reconstruction leaves the capsule available
for inspection. A successful transfer drops its working-machine reference.
T0 resumption is one-use; an error consumes that transfer and does not replay
the entry computation. Costs and rights are not copied into snapshots.

Effects, handlers, staging, guest mutable references, authority-bearing inputs
and rest arguments are declined by the existing pure-fragment admission.
The unused-resource example is rejected before minting the resource. This is
not a demonstration of migrating live authority or multi-shot handler frames.

## Checks and remaining proof work

```sh
clojure -M:memory-probe --check
```

The private-state and bridge portion has 13 tests and 1,616 assertions. The
command now also runs activation-kernel checks, totaling 18 tests and 2,621
assertions; see the [comparison](ACTIVATION.md).
For small programs it pauses after every private transition, reconstructs a
state and finds a matching reachable reference configuration in forward order.
The observer preserves numeric representations, closure aliases, recursive
graphs and pinned bases. A private step may skip administrative T0 states;
transition counts are not equated. Each paused state also resumes through both
T0 drivers. Final states are compared too.

Additional cases cover pending operands, source metadata, larger captures,
tail/non-tail calls, unchanged prepared values, decimal contexts, cross-thread
snapshot resumes, competing transfers, primitive replacement and overflow.
A test deliberately reuses retired raw buffers and verifies that materialized
state is unchanged; application code must still follow the controller leases.

The observer, original-Core index, closure reconstruction and lifecycle
controller are handwritten host code. This is empirical evidence for the
representation relation, not an ansatz-checked simulation theorem. It also
does not prove effect ordering for unsupported effectful programs. The next
formal task is to define the supported graph/layout invariant and show that
private transitions and materialization preserve the chosen reference
observations, with a progress argument for administrative steps.

No new performance result is claimed. The retained memory experiment reports
refer to their recorded source cohort. An index is added only for bridge
preparation; reconstruction and lifecycle/context checks have their own costs
to measure before promoting the tier. The next architectural experiment can
compare prepared activation programs with these node-based states using the
same admission and reconstruction contract.
