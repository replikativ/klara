# Chez compilation and execution experiment

Measured 2026-10-29. Chez is running: the exact sibling revision
`fae51c278e4cb43d89bce43172c5c74ac6b23343` was built as native threaded
x86-64 (`ta6le`), Chez 10.5.0, entirely under `/tmp/klara-chez-empirical`.
The sibling checkout was read only. All five pinned public submodules were
downloaded into that temporary tree; no system install or Klara dependency
change was needed. This supersedes the missing-prerequisites stopping point
in [CHEZ-COMPILER.md](CHEZ-COMPILER.md).

**The useful result is a compiler policy, not a runtime migration:** small safe
Scheme procedures compile in hundreds of microseconds and execute immediately
as native code. An optional source optimizer can be bypassed for modestly lower
latency. That policy does not bound compilation: a 1,024-operation procedure
still takes tens of milliseconds. Ahead-of-time compiled objects remove source
compilation from execution, but require the Chez runtime and preserve Scheme
semantics. These observations support testing a small generic Klara compiler
and AOT artifacts while keeping explicit admission, control and recovery rules.

## Method and limits

[workloads.ss](chez/workloads.ss) contains standalone Scheme analogues of the
first three [current baseline](../baseline/CURRENT.md) programs, plus a ledger:

| Program | Input and result | Representation |
|---|---|---|
| sum | n=10,000; 49,995,000 | Tail-recursive integer sum |
| calls | n=10,000; 50,005,000 | Lexically captured increment procedure called in loop; compiler may inline it |
| copy-vector | n=10,000; `#(49995000 10000)` | Allocate a fresh two-element vector each iteration; no writes to earlier versions |
| ledger | 1,000 deposits over 32 accounts; `(499500 1000 124750)` | Immutable association-list updates, retain every version, query the state after deposit 499 |

The ledger is a useful small versioned data transform with lookup, branching,
recursive update, structural sharing and retained historical roots. It is not
a persistent hash map implementation. The vector is a fresh fixed-size Scheme
vector, not Clojure's persistent vector. They cannot establish collection
speedups over Klara. No Scheme source emitter, guest runtime adapter, managed
references, handler translation, JVM integration or transport is implemented.

All arithmetic uses safe generic Scheme operations, optimization level 2,
without fixnum declarations or unsafe primitives. `compile-interpret-simple`
is false explicitly. Two configurations use identical source:

- **default:** normal `run-cp0` source optimization.
- **no-cp0:** documented `(run-cp0 (lambda (cp0 x) x))`, bypassing cp0 and
  cptypes. Mandatory checking, closure conversion, loop recognition, direct-call
  optimization, register allocation and native emission still run. This is
  not a distinct baseline code generator or a generally unoptimized compiler.

Three sequential fresh processes per mode record first compilation, immediate
first invocation, 200 checked warmup calls, nine samples of 50 invocations, and
nine repeated compilations. Inputs/forms are prepared before timing. Results
are checked against explicit expected values. Compilation includes the public
`compile` call and creation of the resulting procedure; parsing the quoted
source, process startup and harness compilation are excluded. First compilation
means the first compile of that workload in a process; only sum is the first
measured workload in each process. Later workloads share compiler/allocator
state. The two modes reverse order in process 1.

Each AOT object is compiled separately with `compile-file`; each load and its
first call run in a fresh process. Loader timing starts after the harness is
loaded, so it excludes boot and harness compilation. No timing cohort ran
concurrently with another benchmark suite. There is no CPU pinning, controlled
frequency, heap-retention measurement, GC exclusion, allocation measurement or
claim of worst-case latency. Ordinary collections remain part of timings.

Machine: Intel Core Ultra 7 258V, 8 logical CPUs, Linux x86-64
`7.0.0-38-generic`, GCC 15.2.0. Native build uses the project's normal safe
configuration, with curses and X11 disabled, `make -j2`.

## Compilation, first call and warmed calls

All numbers below are **microseconds**. Ranges are across three processes;
warm and repeated-compile rows use each process's median sample. First-call
and first-compile rows have one observation per process. They are diagnostic
cohorts, not confidence intervals.

| Program | Default first compile | Default repeat compile | No-cp0 repeat compile | Default first call | Default warm call | No-cp0 warm call |
|---|---:|---:|---:|---:|---:|---:|
| sum | 261–270 | 166–179 | 126–157 | 5.57–5.95 | 5.59–5.78 | 5.69–5.89 |
| calls | 164–183 | 158–165 | 132–136 | 7.62–8.61 | 7.46–7.96 | 7.91–8.28 |
| copy-vector | 222–230 | 210–214 | 169–187 | 26.96–34.81 | 13.82–14.54 | 13.98–14.61 |
| ledger | 581–692 | 542–582 | 463–474 | 39.51–47.14 | 35.12–35.95 | 37.01–37.63 |

Bypassing cp0 lowers repeated compile latency on these programs, while the
ledger loses some warmed throughput. The small loops start near their warmed
throughput. Allocating programs show larger first-call differences, especially
in fresh AOT processes below; no causal allocation or cache profile was taken.
Chez's scalar sum is not faster than the historical compiled Clojure control
(3.14–3.25 microseconds). This experiment makes no cross-language speedup claim:
the host representations, arithmetic, compilation and measurement protocols
differ. The important contrast with guest interpretation is removal of guest
dispatch, not a measured Chez-versus-Klara backend comparison.

[scale.ss](chez/scale.ss) generates a lambda with sequential `let*` additions;
form generation and parsing are outside the timed public `compile` call. Five
compilations per size, three fresh processes per mode. This separate phase ran
after the primary cohort, default mode before no-cp0 in each pair:

| Sequential additions | Default compile median, µs | No-cp0 compile median, µs |
|---:|---:|---:|
| 16 | 568–616 | 502–741 |
| 64 | 1,110–1,221 | 1,050–1,320 |
| 256 | 6,383–6,677 | 4,850–5,080 |
| 1,024 | 46,547–48,676 | 36,420–36,985 |

This simple source-size probe already defeats a blanket submillisecond claim.
It is neither adversarial macro expansion nor an upper bound. A predictable
interactive baseline needs size/work admission and a fallback policy in
addition to a reduced optimizer budget. `cp0-effort-limit` bounds individual
inlining attempts; it does not bound macro expansion or every backend pass.

## Ahead-of-time objects

Default safe code, three independent object builds and fresh loading processes:

| Program | compile-file, µs | Native object load, µs | First call, µs | Warm call, µs |
|---|---:|---:|---:|---:|
| sum | 788–817 | 90.8–94.1 | 5.24–5.59 | 5.35–5.58 |
| calls | 758–782 | 87.9–110.3 | 7.43–8.19 | 7.67–7.74 |
| copy-vector | 441–507 | 90.6–95.3 | 109.5–117.1 | 14.18–14.32 |
| ledger | 873–908 | 102.3–111.6 | 104.4–110.1 | 35.52–35.99 |

`compile-file` includes source reading, file compilation, serialization and
output; it is not directly comparable to expression compilation. The objects
contain native code and load without source compilation. They are deployment
artifacts requiring a compatible Chez target/runtime, not standalone OS
executables, heap snapshots or portable serialized closures. The raw object
byte sizes are recorded with compile-file samples; generated binaries stay in
`target/chez-empirical`, outside the tracked experiment.

Nine separate minimal script processes took **44.1–54.8 ms wall time, median
46.6 ms**, including subprocess creation, boot and minimal script loading.
Thus a fresh process for every tiny call would dominate the kernel by orders
of magnitude. A persistent worker or embedded runtime is a separate integration
choice; neither transport/serialization nor native/JVM ownership was measured.
Chez also offers `compile-program`, libraries and boot-file packaging; this
cohort tests only compile-file/load, not a bundled executable or its deployment
footprint. Klara's JVM compiler can likewise emit/cache artifacts ahead of
execution; those need guest/runtime/target versions and assumption metadata.

## Semantics checked and semantics still owed

[semantics.ss](chez/semantics.ss), whose [raw output](chez/results/semantics.tsv)
is preserved, verifies one million proper tail calls and reuse of a native
multi-shot continuation twice. Its captured mutable box advances from 1 to 2
to 3 across the shots: continuations share referenced state. This demonstrates
control capture and explicitly does not demonstrate forked application memory,
delimited Klara resumptions, cleanup, cancellation or affine authority.

The same script verifies exact promotion of `Long/MAX_VALUE + 1` to
9,223,372,036,854,775,808 and a Chez greatest fixnum of 2^60−1. Klara's checked
Long overflow cannot be implemented as generic Scheme addition. The timed
integer workloads stay within both domains, but correctness outside them
requires Klara numeric adapters and explicit guard/fallback behavior. Scheme's
empty list is true; nil handling and operand order also need guest lowering.
The local closure may be inlined or have captures trimmed; that is not
permission to alter Klara's authority-reachability envelope. Native Scheme
continuations cannot be used to clone arbitrary JVM activations.

## Transplantable choices

1. **Compile normal bodies early.** Compile admitted lexical control and local
   calls to host procedures while retaining generic Klara helpers. This removes
   guest dispatch without requiring global type inference. Compare existing
   generic JVM emission and checked primitive emission over exactly the same
   guest program before selecting Chez as a substrate.
2. **Make optional optimizer work explicit.** Chez's public hook demonstrates
   that source optimization policy can be varied independently of safety and
   native emission. In Klara, keep admission, primitive identities, checked
   arithmetic and recovery obligations fixed while skipping optional expensive
   passes. Measure compiler size/latency, declines and whole-call break-even.
   No-cp0 is evidence for separation, not a bound or complete design to copy.
3. **Use AOT where reuse and deployment justify it.** Persist versioned code
   artifacts and validate their code basis/runtime assumptions at entry. Build
   world-specific code identities without mutating one global Scheme namespace.
   Interactive procedures can compile on demand; stable definitions can compile
   before deployment. Neither requires waiting for hotness as the sole policy.
4. **Keep execution/control metadata canonical.** Chez owns its stack, collector,
   tail-call ABI and continuation representation. Borrow the principle of
   explicit compiler stages and code lifecycle; its native stack machinery is
   not a JVM transplant. Klara still needs canonical captures, code/state/rights
   contexts, admission, recoverable boundaries and exactly-once effects.

There is enough evidence to pursue a bounded emitted-body experiment, not
enough to change Klara's production runtime or add Chez as a dependency. A
future Scheme backend should first implement an explicitly admitted pure guest
subset with checked arithmetic and exact value adapters, then compare its
end-to-end compilation, transport, entry and execution to the JVM alternatives.
The ledger's persistence is an example data structure, not a supplied world
model or authority system.

For Klara, deterministic guest transitions and explicit compilation policy are
useful reproducibility goals, but neither an interpreter nor AOT compilation
guarantees deterministic wall-clock cost. JVM tiering, scheduling and GC still
affect a JVM interpreter. Chez native compilation removes dependence on later
profile-driven code generation for these procedures, while allocation, caches,
GC and compilation-size effects remain. A deployment that forbids runtime
compilation should require prebuilt admitted artifacts explicitly; it should
not rely on a hotness heuristic merely happening not to trigger.

## Reproduction and evidence

From the Klara root, with network access for the public pinned dependencies:

```sh
sh experiments/interpreter/chez/build.sh ../ChezScheme /tmp/klara-chez-reproduce
export SCHEME=/tmp/klara-chez-reproduce/source/ta6le/bin/ta6le/scheme
export SCHEMEHEAPDIRS=/tmp/klara-chez-reproduce/source/ta6le/boot/ta6le
sh experiments/interpreter/chez/run.sh target/chez-empirical-reproduce
```

No install is required. [Raw TSVs and summary](chez/results/summary.tsv),
dependency archive hashes, configure log and final build output live under
`chez/results/`. Each sample row is process, mode, workload, phase, sample,
nanoseconds, result (or compiled object byte size). Startup rows are sample and
wall nanoseconds. [summarize.py](chez/summarize.py) checks three process groups
and produces ranges of process medians. Compilation scaling and startup are
separate phases, not mixed into warm-call results.

Primary implementation evidence is available in the exact sibling checkout:
`s/compile.ss` around 1800 separates expansion/validation, optional cp0 and
mandatory backend work; `s/cpnanopass.ss` around 10900 shows loop/closure/direct
call lowering and native generation. `csug/system.stex` documents `run-cp0`,
`compile-file`, `compile-program` and boot-file construction. The experiment
uses those public interfaces without copying compiler source or private IR.
