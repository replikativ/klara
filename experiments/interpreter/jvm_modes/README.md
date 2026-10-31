# JVM bytecode interpretation and C2 control

Diagnostic measured 2026-10-30 on Intel Core Ultra 7 258V, Linux x86_64,
Oracle GraalVM JDK `25.0.1+8-LTS-jvmci-b01`. This is a Java primitive-loop
control, not a Klara or SCI benchmark. It measures two different loop bodies:
wrapping Java Long addition, and checked `Math.addExact` addition for both
counter and accumulator. Both sum 0 through 9,999 and return 49,995,000.

Three sequential fresh processes per execution mode, 256 MiB heap, nine
samples of 100 calls. The interpreter gets 20 warmup calls; C2 gets 20,000.
Kernel inlining into the harness is disabled in both configurations. A volatile
input prevents treating the limit as a compile-time constant; a volatile sink
retains every measured result. Setup, compilation, logging output and startup
are outside the timed loops. Each final sample result is checked.

| Body, n=10,000 | `-Xint`, µs/call | C2, µs/call |
|---|---:|---:|
| Wrapping addition | 40.45–41.98 | 2.15–2.22 |
| Checked addition | 307.78–319.00 | 2.86–2.94 |

Ranges are per-process medians. The corresponding paired process ratios are
approximately 19× and 108×. These are examples of workload dependence, not a
general interpreter slowdown factor. There is no CPU pinning, first-call study,
confidence interval or broad workload corpus.

`-Xint` disables JIT compilation; this does not isolate just the loop from its
otherwise interpreted Java helpers. The checked body therefore also pays for
interpreted `Math.addExact` helper calls. C2 can inline/optimize those helpers.
The C2 runs explicitly disable JVMCI compilation and tiered compilation and
use `-Xbatch`. The default JVM here uses Graal, so the previous ordinary JVM
benchmarks should not be relabeled as C2 results. The
[compiler evidence](results/compiler-evidence.txt) records actual `c2` native
methods for both kernels, including ordinary and OSR entries in each process.
Complete generated compilation logs remain under `target/jvm-modes`.

The earlier [SCI cohort](../../baseline/CURRENT.md) measured approximately
121–124 µs for its checked summation loop on a normally warmed JVM. That is
different source, numeric machinery and measurement protocol. It is not a
paired ranking against this Java control. SCI's evaluator implementation can
itself run as JIT-compiled host code; “SCI interpreter” does not imply that
the JVM is interpreting all of SCI's bytecode. Running SCI under `-Xint` would
be a separate comparison.

```sh
sh experiments/interpreter/jvm_modes/run.sh
```

Recorded [interpreter](results/int-0.tsv) and [C2](results/c2-0.tsv) reports
have peers numbered 1 and 2 and retain all samples, flags and runtime identity.
New runs write under `target/jvm-modes`. No runtime/compiler code is changed
by this diagnostic.
