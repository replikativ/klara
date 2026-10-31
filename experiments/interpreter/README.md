# Generic interpreter driver comparison

The separate [private mutable CEK experiment](MEMORY.md) explores a more
substantial storage change for a closed pure fragment, including snapshot/thaw
checks. Its results and restrictions are separate from this default-driver work.

This experiment compares two drivers over the same T0 implementation and
source cohort. `drive-reference` follows explicit transitions. The default
driver fuses immediate operand evaluation, keeps common machine registers in
Clojure loop locals and uses a guarded fixed-arity scalar primitive path.
Klara's compiler hooks are disabled throughout.

The change targets temporary allocations, rather than changing guest memory
semantics. Suspended continuation frames, closure environments and argument
values remain persistent data. Handler/capture/deopt boundaries retain their
existing representations. No new mutable stack, Java helper or `deftype`
representation is introduced by this experiment.

## Reproduce

Run sequentially with other verification jobs stopped:

```sh
clojure -M:interpreter-bench 0
clojure -M:interpreter-bench 1
clojure -M:interpreter-bench 2
clojure -M experiments/interpreter/summarize.clj
```

Each JVM warms both drivers with 40 calls per workload, then collects nine
samples of five calls. Sample order alternates; process parity changes which
driver starts. Preparation/expansion is excluded. The same closure is used
for both drivers, every returned value is checked, and raw results include
all samples, source hashes and JVM configuration. Allocation is measured on
the current thread, including measurement overhead.

The summarizer rejects mixed source/runtime cohorts. Its speedup is a ratio
of reference/fused medians within each process; reported ranges span three
processes. These short runs do not establish steady-state confidence
intervals, general language performance or application throughput. Exception
and staging workloads have different input sizes from the pure loops.

## Recorded results

The [raw reports](results/process-0.edn), [aggregate](results/summary.edn) and
[table](results/summary.tsv) record three sequential JVMs on an Intel Core Ultra
7 258V, Linux x86_64, JDK `25.0.1+8-LTS-jvmci-b01` and Clojure 1.12.4, with
JVMCI enabled and a 1 GiB heap. Source hashes identify the actual measured
working tree. Speedup and allocation reductions below are within-process
comparisons, with ranges across the three processes:

| Workload | Input n | Reference/fused time | Allocation reduction |
|---|---:|---:|---:|
| Summation | 1,000 | 1.17–1.78× | 64.5–68.3% |
| Local calls | 1,000 | 2.11–2.40× | 60.0–63.8% |
| Persistent vector updates | 1,000 | 1.79–1.94× | 54.5–54.7% |
| Host callbacks | 1,000 | 1.11–1.63× | 43.1–44.1% |
| Resuming handler | 100 | 1.05–1.21× | 48.2–52.5% |
| Multi-shot capture | 100 | 1.16–1.27× | 33.7–35.5% |
| Exception handling | 100 | 1.14–1.49× | 50.4–53.7% |
| Staging and running code | 10 | 1.10–2.27× | 31.6–35.3% |

All measured process medians improve, but timing variation is substantial.
For example, reference summation ranges from 2.61 to 8.68 ms and fused summation
from 2.15 to 4.87 ms across JVMs. The allocation reduction is stronger evidence
than a precise latency forecast. These experiments do not isolate the benefit
of each change or establish that all programs improve. Generic interpretation
remains expensive; this is an incremental improvement, not parity with SCI,
host Clojure, compiled Java or a low-level interpreter.

## Safety and correspondence

The scalar shortcut accepts only selected original arithmetic functions and
zero to two operands of exact `Long`/`Double` class. Actual function identity
is checked before invocation. Custom Number implementations, overridden
functions, other numeric representations and larger arities fall back.
Checked arithmetic and errors use the existing functions and handler path.
This does not infer a primitive loop or admit arbitrary host effects.

`test/klara/driver_test.clj` compares values, errors, printed output and effect
traces for both drivers, including repeated resumptions and discarded effects.
Generated arithmetic expressions also compare with host Clojure. The core
suite and specialization verification run the default driver; evaluator,
authority, deoptimization and staging suites have additionally been exercised
with the reference driver selected. `step-state` is unchanged, so bounded
planning still counts the original explicit transitions.

These are implementation checks, not a complete refinement proof. The
[interpreter guide](../../doc/interpreters.md) describes the formal and tested
boundaries. The older [SCI/Clojure diagnostic](../baseline/README.md) retains
its original, pre-optimization source cohort.
