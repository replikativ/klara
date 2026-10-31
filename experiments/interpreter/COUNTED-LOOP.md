# Checked counted loops and backedge recovery

This extends the [scalar block refinement](REFINEMENT.md) to a bounded family
of actual Core loops. It compares existing interpretation with two hosted
emitters, retaining an explicit recovery state at the loop condition. It is an
experiment, not registration of another production tier.

## Admitted source and simultaneous updates

The source has one input, a nonnegative Long limit, two loop variables and a
nonnegative Long seed:

```clojure
(fn [n]
  (loop [i 0 s 0]
    (if (< i n)
      (recur (+ i 1) (+ s (* i i)))
      s)))
```

The accumulator RHS can contain scoped locals, sequential `let`, nonnegative
Long literals, and exact binary `+`/`*`. It reads the old `i` and `s`. The loop
must increment `i` by exactly one and return `s` at exit. The exact Core
recognizer rejects different predicates, captured input reads in the RHS,
different transfers, effects, handlers and arbitrary calls. It independently
reconstructs the complete expected Core shape before accepting its CodeID.

Both RHSs lower to separately validated scalar blocks. The emitted code first
binds `next-index`, then `next-acc`, and only then commits them with `recur`.
Changing `i` before computing `s+i` would turn the first summation update into
1 instead of 0; the tests preserve this rejection example.

## Checked model and remaining bridges

[`counted_loop_model.clj`](../../verification/consolidation/counted_loop_model.clj) defines a
two-field scalar state, ordered checked updates and a structurally terminating
finite driver. The twelve named checked statements cover:

- Composition of the two per-source scalar block receipts into an equivalent
  step; both RHSs use the same old environment.
- Lifting step equivalence through any finite number of iterations.
- Splitting a finite run into two chunks, preserving successful states and
  overflow failure.
- Reading the committed index and accumulator from their new slots.
- The decreasing remaining-count invariant, loop entry/exit arithmetic,
  counter capacity, and a bounded chunk end index.

The per-source loop receipt binds the actual source CodeID and both scalar
receipts to a kernel-checked finite-run equality, for every model capacity,
iteration count and initial scalar state. A wrong accumulator block cannot be
admitted merely because its reads and writes are well formed.

This does not prove the full concrete Core CEK loop correct. The exact Core
decoder, Long/Nat encoding, actual predicate and `min` implementation, hosted
form emission and JVM execution remain tested implementation bridges. In
particular, the chunk-end theorem assumes its quota is bounded by the remaining
count; tests exercise the host calculation that establishes that bound.
The imported Init TRUST boundary remains as documented for the scalar models.

## Budget outside the hot loop

An iteration budget counts **complete source loop iterations**, rather than
CEK transitions. For an admitted state, entry computes:

```clojure
(+ index (min fuel (- limit index)))
```

This stopping index is between the current index and the limit. Subtraction
and addition fit Long under `0 <= index <= limit <= Long/MAX_VALUE`.
The loop compares against the stopping index; it neither decrements fuel nor
checks a separate fuel condition on each iteration. Zero budget leaves a
pending loop paused. A state already at the limit completes with zero budget.

There is no interior suspension inside an RHS. If arithmetic fails, no new
snapshot is returned and the immutable input snapshot remains available. This
does not provide general exactly-once effects or report partial CPU consumption
on failure. Instruction accounting, interrupt timing and elapsed time are not
observations covered by the model equality.

## Two emitted bodies and the reference state

[`counted_loop.clj`](../../verification/consolidation/counted_loop.clj) emits the same validated
block structure in two ways:

| Body | Numeric execution | Entry contract |
|---|---|---|
| Generic | Boxed locals and captured, fixed-site IFn arithmetic/comparison calls | Exact nonnegative Long inputs/state; stable primitive roots |
| Primitive | Primitive Long locals, direct comparisons and checked Long arithmetic | Same contract |

Admission checks input/state layouts, source identity, pinned basis and the
anchored `+`, `*`, `<` helpers once per chunk. There are no guest callbacks
between admission and use. Concurrent arbitrary host redefinition is outside
this region contract. Generic emission means generic numeric calls within this
admitted fragment, not support for every numeric representation.

Bytecode inspection of the summation bodies confirms primitive `lload/lstore`,
`lcmp` and `Numbers.add:(JJ)J` calls, with no `IFn.invoke` in the primitive
loop. The generic body uses `IFn.invoke(Object,Object)`. Thus Klara's emitter
chooses the primitive loop representation before host JIT compilation. The JVM
still supplies machine-code generation and its optimizations.

Snapshots are immutable maps containing the source identity, pinned basis,
limit, index and accumulator. Running two chunks from one snapshot needs no
shared mutable working store. `reference-state` constructs the corresponding
logical T0 loop-condition configuration, retaining the original self-closure
and its capture prefix. `resume-reference` runs that state with compiler hooks
disabled. Tests compare reconstructed graph signatures to reachable T0 states
at every backedge in the selected cases and resume each to completion.

Hosted callers can fabricate maps; these snapshots are not authenticated
reachability certificates or a sandbox interface. Reachability from the initial
call is established for states produced by the admitted execution path. This
fragment does not solve mixed-world closure conversion or general native-stack
capture.

## Recorded comparison

Measured 2026-10-30 in three sequential fresh JVMs on an Intel Core Ultra 7
258V, Linux x86_64, JDK `25.0.1+8-LTS-jvmci-b01`, Clojure 1.12.4, a 1 GiB
heap and 16 MiB stack. JVMCI is enabled. Each engine receives 200 interleaved
warmup calls per input size, followed by nine samples of ten invocations, with
rotating engine order. There is no CPU pinning or guaranteed steady state.
The source forms used for the Clojure controls expand to the exact same Core
CodeIDs as the decoded loops. Compiler entry hooks are disabled for T0 controls.

The table gives ranges of process medians, **microseconds per invocation at
n=10,000**. Full emitted calls include root/layout checks, immutable snapshot
construction and result projection. Body-only calls return/project the final
state vector but exclude admission. Neither includes compilation.

| Execution | Summation | Sum of squares |
|---|---:|---:|
| Compiled Clojure control | 3.22–3.44 | 4.27–4.40 |
| Generic emitted body | 3.06–3.27 | 3.95–4.10 |
| Primitive emitted body | 2.64–2.96 | 3.46–3.58 |
| Full generic emitted call | 6.39–7.77 | 8.09–8.27 |
| Full primitive emitted call | 4.02–4.55 | 4.86–5.01 |
| Private node interpreter | 2,263–2,487 | 2,924–3,032 |
| Default fused T0 | 9,422–10,133 | 11,962–12,182 |
| Reference CEK driver | 21,087–22,568 | 26,152–26,844 |

Body-only current-thread allocation is about 238 bytes per call for generic
emission and 214 bytes for primitive emission, at both measured sizes. Full
calls allocate about 2.29 KB and 2.26 KB respectively. Allocation includes
harness overhead. Thus this warmed JVM also eliminates iteration-proportional
boxing in the generic emitted bodies on these stable sites. The generic result
does not promise equivalent optimization for arbitrary dynamic calls; the
primitive bytecode establishes its layout without waiting for such inference.

Preparation is **not yet a cheap baseline compiler**. The cold proof-model
bootstrap takes 3.33–3.45 seconds, separately from namespace startup. Each
workload then has one measured preparation per process:

| Phase | Summation, ms | Sum of squares, ms |
|---|---:|---:|
| Per-source certificate construction | 70.3–80.3 | 90.5–99.7 |
| Receipt admission and both emitters | 21.6–21.9 | 26.6–29.4 |
| Ordinary Clojure control compilation | 0.427–0.685 | 0.345–0.404 |

These preparation ranges are individual observations, not repeated-compile
medians. They exclude dependency/namespace loading and include the reported
public preparation phases; the emitter phase constructs two variants. A
cached generic lowering theorem with cheap instantiation is a next candidate
for reducing symbolic proof generation. AOT can move this work out of request
execution, but artifact persistence/admission is not implemented by this probe.

The [summary](counted-loop-results/summary.edn),
[tabular results](counted-loop-results/summary.tsv), and raw reports
([0](counted-loop-results/process-0.edn), [1](counted-loop-results/process-1.edn),
[2](counted-loop-results/process-2.edn)) retain samples, source hashes, emitted
forms, VM arguments and preparation measurements. The
[primitive](counted-loop-results/primitive-bytecode.txt) and
[generic](counted-loop-results/generic-bytecode.txt) disassemblies are from the
same sum-emission forms; generated class names are incidental REPL identities.
Retained heap, GC cost and hardware counters were not measured.

An earlier two-process pilot with a separate fuel counter remains generated
under `target/counted-loop/fuel-pilot`; it is not mixed into this cohort.
The experiment does not automatically select/install emitted regions or extend
their pure-fragment capabilities. Its evidence supports removing dispatch and
lifting region constraints before expanding the interpreter representation.

## Reproduce

```sh
clojure -M:runtime-refinement
clojure -Sdeps '{:paths ["src" "test" "experiments"]}' -J-Xmx1g -J-Xss16m -M -m interpreter.counted-loop-bench 0
clojure -Sdeps '{:paths ["src" "test" "experiments"]}' -J-Xmx1g -J-Xss16m -M -m interpreter.counted-loop-bench 1
clojure -Sdeps '{:paths ["src" "test" "experiments"]}' -J-Xmx1g -J-Xss16m -M -m interpreter.counted-loop-bench 2
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m interpreter.counted-loop-summary
```

Run benchmark processes sequentially. The summary rejects mismatched
source/runtime cohorts. Preparation, proof-model bootstrap, per-source
certification and emission are reported separately from execution. Body-only
measurements exclude admission; ordinary calls include the whole current
wrapper and snapshot/result construction. These are two diagnostic programs,
not language-wide or worst-case latency results.
