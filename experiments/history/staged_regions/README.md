# Staged scalar lifecycle diagnostic

Load `bench.clj` in a persistent Clojure REPL rooted at the repository, then
call `(staged-regions.bench/run!)`. The JDK compiler must be available. The
example world and compiler are rebuilt; both execution paths are warmed across
all sizes before timing. No additional JVM is launched. `results.edn` records
all samples; `kernel.java.txt` is the generated residual body.

Recorded on GraalVM 25.0.1, `UseJVMCICompiler=true`, one process:

| Iterations | Independent primitive Clojure | Full guarded JVM entry | T0 |
|---:|---:|---:|---:|
| 32 | 0.059 µs | 1.331 µs | 176.6 µs |
| 256 | 0.192 µs | 1.434 µs | 1352.5 µs |
| 1024 | 0.581 µs | 1.823 µs | 5150.3 µs |

The classfile is 894 bytes. Early model generation plus all example definitions
took 2.38 ms, warmed preparation 20.51 ms, and installation 0.23 ms. The full
entry path includes layout, world and handler admission. An entry/body ablation
and allocation profile are still needed to attribute the gap to ordinary
primitive Clojure. This is not a claim of parity with handwritten numerical code.

The approximate compile-amortization counts are 118, 16 and 4 calls against
T0, excluding generation, profiling and installation. They describe only this
warmed compiler process. First-use javac initialization can cost substantially
more. The fixed-order, single-process samples are diagnostics, not statistically
controlled publication results. Retained memory, profiler cost, cold-start
compilation, multiple application families and multi-process confidence
intervals remain unmeasured.

Targeted correctness tests are in `klara.staged-compile-test`; the full design
and implementation boundary are in `doc/engineering/runtime.md`.
