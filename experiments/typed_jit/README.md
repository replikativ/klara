# S20: typed Java loop probe

Start one Clojure REPL at the repository root:

```sh
clojure -J-Xmx1g -J-XX:+UseSerialGC -M
```

At its prompt run:

```clojure
(load-file "experiments/typed_jit/run.clj")
```

`emit.clj` compiles two actual Klara worlds with `g(x)=2*x` or `3*x` and
the same `f(n)=sum(g(i))`. It accepts only the exact IR tree in
`checked-shape` and requires the existing proved `Long -> Long` return
layout and pinned `g` value-ID guard. It writes Java source to `generated/`.
`run.clj` invokes `javax.tools.JavaCompiler` inside the same REPL, loads
the resulting classes through a new class loader, checks values, a stale
guard and arithmetic overflow, then benchmarks generated and independent
Java loops. It also benchmarks Klara's compiled residual-call loop in the
same process. No benchmark JVM restart is required. Classes are compiled
under `/tmp/klara-s20-classes`.

The generated Java is a **performance and ABI probe**, not a Klara
executable. It has a `(Context,long) -> long` signature, a guard before a
checked primitive loop and a direct typed `g(long) -> long`. Its `Context`
contains only one `g` value ID. It lacks the real pinned root and caller
identity checks, transitive read recording, cache-generation and feedback
checks, handler admission, authority state, general input dispatch, and a
T0 frame reconstruction path. It must not be installed in `stage`.

The benchmark measures whole calls with a volatile result sink, 10,000
warmups and nine batches of 10,000 calls. The samples share a JVM but
different call shapes and class loaders, so they are a feasibility signal,
not a causal estimate of a future production compiler. The boxed Java
callback can be inlined and scalar replaced by HotSpot in this monomorphic
sample; its low allocation does not imply Klara's boxed call path is cheap.

See `doc/engineering/performance.md` for measurements and the required compiler
integration steps.

## S21: reusable typed regions and Graal inspection

`regions.clj` replaces exact-tree recognition for the new experiment with
an abstract interpreter over scalar Klara IR. It accepts Long/Boolean
constants, locals, lets, conditionals, checked scalar primitives, known
world calls, and directly entered single tail loops. It checks every
backedge against the entry layout. Calls require a previously analyzed
callee summary. Typed nodes retain result layouts; functions retain input
requirements and world dependencies. Direct calls and compiler inlining
are two emissions from the same typed representation. The experiment still
uses Java source plus in-process javac, not a dedicated bytecode writer.

The host adapter is deliberately restricted to a unary Long entry with
one pinned `g` dependency. It checks a value-ID token, not a real root or
full Klara admission. Feedback polling is omitted. These classes must not
be installed as Klara executables. The analyzer and emitter are Clojure
seed code; probabilistic candidate selection and a Klara-written JIT policy
are not implemented here.

For graph inspection, start a persistent REPL once with:

```sh
clojure -J-Xmx1g -J-XX:+UseSerialGC -J-XX:-UsePerfData \
  -J-Djdk.graal.Dump=:1 \
  '-J-Djdk.graal.MethodFilter=klara.typedprobe.Region0.*,*body*.invoke' \
  -J-Djdk.graal.DumpPath=/tmp/klara-s21-graphs \
  -J-Djdk.graal.PrintGraph=File -J-Djdk.graal.PrintBackendCFG=true -M
```

Then evaluate:

```clojure
(load-file "experiments/typed_jit/capture-regions.clj")
```

This generates four program pairs, compiles both variants in-process,
compares 152 values/errors against T0, checks eight mismatched guards and
two unsupported programs, then benchmarks under JFR. The recording is
`/tmp/klara-s21-regions.jfr`; a textual summary is saved in this directory.
For checks without timing, load `run-regions.clj`. For another warmed
measurement in the same REPL, call `(region-bench!)`.

Graal must be the enabled JVMCI compiler to reproduce the graph experiment.
Open `.bgv` files in IGV; `.cfg` files contain textual HIR and backend dumps.
To regenerate the compact graph inventory:

```sh
python3 experiments/typed_jit/summarize-graphs.py /tmp/klara-s21-graphs
```

Dumping and JFR affect compilation and timing. Use this run to investigate
generated code, not as a publication performance result. Graph counts
include cold paths; OSR and ordinary compilations must be distinguished.

## S22: shared requirements and AOT artifacts

In the same persistent REPL:

```clojure
(load-file "experiments/typed_jit/run-aot.clj")
```

The experiment builds `/tmp/klara-s22-old.edn` and
`/tmp/klara-s22-new.edn`. Each file contains base64 JVM classfiles,
class digests, implementation/target versions, source CodeIds, dependency
guards, input layouts and read sets. `aot/load!` validates those fields and
defines the saved classes in a fresh loader. It does not analyze or emit
code or invoke javac. The test disables compiler/analysis/build functions
while loading and invoking to verify that boundary.

`src/klara/compile/requirements.clj` defines the data-only scalar requirement
record used by both S21's region analyzer and this AOT path. Invoking a
loaded artifact checks its source/dependencies against the supplied root,
argument layouts and handler conditions before running its primitive body.
Unsupported arguments or stale definitions use T0 with the supplied root.
Transitive reads are recorded anew in each invocation's recording scope.

This is a trusted local cache experiment, not a production stage ABI.
Artifacts carry no semantic proof; hashes detect mismatches and do not
make untrusted bytecode safe. Builds still use the existing compiler and
JavaCompiler, and loading currently fingerprints the local source checkout.
No automatic artifact discovery, startup integration, memoized admission,
general handler/authority compilation, or native AOT is provided.

Results and remaining integration work: `doc/engineering/performance.md`.
