# Performance: where this design can go

Status: assessment and plan, written after P1–P5 of this iteration. The
question: with a native host (C99, compiled ahead of time; GraalVM native
image as a first step), could Klara's JIT be competitive with V8 or Graal,
in completeness and in speed?

## Where we are

On the JVM, Klara's JIT is a specialization layer above HotSpot. Klara
decides what to specialize (specializers, the investor), relates the result
to the reference (the checker, certificates), and leaves through frame
states. HotSpot does the machine-level work: register allocation, its own
inlining, escape analysis, type-profile speculation. Measured consequences:

- speculating that numbers are longs bought nothing (06-speculation.md §4):
  HotSpot already removes the boxing;
- compiled Klara is about as fast as Clojure where the specializer removes
  the interpretive overhead (showcases 1–3: 20–60× over the interpreter);
- the interpreter costs about 0.6 µs per Klara call, roughly ten times SCI.

So today's speed is HotSpot's, plus what staging removes. A native host has
no HotSpot underneath.

## What V8 and Graal have that we do not

| | V8 / Graal | Klara now |
|---|---|---|
| first tier | register bytecode, nanoseconds per operation | CEK machine, a frame object per step |
| baseline compiler | microseconds per function | none |
| optimizing compiler latency | milliseconds | 10–90 ms (Klara specializer, checker, Clojure compiler, HotSpot) |
| coverage | everything compiles | a subset; the rest stays interpreted |
| object model | hidden classes / shapes, inline caches | persistent maps, host dispatch |
| numbers | tagged/unboxed | boxed, HotSpot unboxes |
| escape analysis, scalar replacement | own | HotSpot's |
| GC | own, generational, precise | JVM's |
| verified optimizations | no | yes (definitional checks, certificates) |
| invalidation | code dependencies | world premises, exact and per world |
| speculative/parallel compilation | concurrent compiler threads | isolated forks (jobs), adoptable |
| multi-shot continuations in compiled code | no | leave and resume via frame states |

GraalVM native image is closed-world: as far as we know it does not load
new bytecode at run time by default (newer releases experiment with run-time
class loading). Under native image the current JIT, which emits bytecode
through `eval`, does not work; the interpreter and AOT given a profile do.
A native host needs its own code emission.

## Where the approach is strong

- **Staging instead of automatic partial evaluation.** Staged interpreters
  produce code as good as partial evaluation (Amin and Rompf, *Collapsing
  Towers of Interpreters*, POPL 2018; LMS), with the program in control:
  showcase 1. Truffle's partial evaluation needs annotations and can explode;
  a specializer states what it does.
- **Domain knowledge.** User specializers know what no general JIT can:
  an interpreter's program, a DSL's algebra, an invariant proved in ansatz.
  This is where Klara can be ahead of V8 rather than behind.
- **Exact invalidation** from world generations; old worlds keep their code.
- **Isolation**: exploration in parallel forks is safe by construction.
- **Functional but in place** (P6): reference counting with reuse
  (Perceus, Koka) makes functional code competitive with C on the workloads
  where it applies.

## The path, in order

1. **A first tier without cliffs.** Keep the CEK machine as the semantics
   but run on the host stack until a continuation is captured (one-shot fast
   path; copy frames on capture), with frames allocated only for effects and
   leaves. Target: SCI's speed or better.
2. **Compile everything.** Lower all of Core, including `try`, `letrec`,
   interop and handlers, leaving through frame states where needed.
   Completeness before peak speed.
3. **A low-level IR between Core and the host** (SSA, explicit
   representations: tagged or unboxed numbers, shapes for maps with known
   keys from profiles, arrays), produced by Klara specializers and checked
   as a refinement of Core. Backends: JVM bytecode directly, then C.
4. **A native backend.** C emitted per candidate and compiled at run time
   (a small C compiler for fast tiers, an optimizing one for the top tier),
   or machine code through an existing code generator; with the runtime's
   own GC, safepoints and frame-state maps. Native image first for the
   runtime itself, with AOT given a profile.
5. **Ownership** (P6) for in-place updates without visible mutation.

## Measured (Are We Fast Yet?, ms per iteration)

`clojure -M:awfy`, same machine, after the investor has run (2026-11-01, after
the review fixes):

| benchmark | node (V8) | Clojure (HotSpot) | Klara interpreted | Klara compiled |
|---|---|---|---|---|
| Mandelbrot | 24 | 29 | 13,000 | 30 |
| Sieve | 0.010 | 0.009 | 6.9 | 0.35 |
| Towers | 0.068 | 0.26 | 23 | 0.83 |
| List | 0.015 | 0.037 | 19 | 0.52 |

**Correction (2026-11-01).** The numbers above time each Klara iteration as
an `eval-string` of an `ns` form and the call, which costs about 0.46 ms by
itself: more than a whole Sieve run in Clojure. The harness now runs the
calls in batches inside one evaluation and subtracts an empty batch. With
the staged interpreter as the default specializer, on a busier machine:

| benchmark | node (V8) | Clojure (HotSpot) | Klara interpreted | Klara compiled | Klara / Clojure |
|---|---|---|---|---|---|
| Mandelbrot | 36 | 42 | 15,600 | 44 | 1.05 |
| Sieve | 0.019 | 0.017 | 23 | 0.036 | 2.1 |
| Towers | 0.10 | 0.46 | 35 | 0.49 | 1.07 |
| List | 0.027 | 0.067 | 75 | 0.44 | 6.6 |

So compiled Klara is at Clojure's speed on three of the four; List (calls of
tiny functions on records) is the real gap.

**After the investor and record fixes (2026-11-01, quieter machine).**
Records are host classes (field reads were a linear search of an array map,
22% of List); the investor tiers by interpreted time spent, compiles as is
past the baseline (so small callees no longer leave compiled callers
entering the interpreter), runs between forms and promotes baseline code
from counted entries (L4.jit.tiers, L4.jit.trigger); the harness warms up
with the automatic investor and stops it before timing:

| benchmark | node (V8) | Clojure (HotSpot) | Klara interpreted | Klara compiled | Klara / Clojure | Klara / node |
|---|---|---|---|---|---|---|
| Mandelbrot | 24 | 27 | 9,300 | 27 | 0.98 | 1.1 |
| Sieve | 0.0098 | 0.0086 | 7.0 | 0.011 | 1.23 | 1.1 |
| Towers | 0.066 | 0.26 | 30 | 0.48 | 1.85 | 7.3 |
| List | 0.013 | 0.035 | 22 | 0.063 | 1.77 | 4.7 |

Towers and List vary between runs with the investor's choices (whether the
default specializer's inlining of a small callee measures as faster).

**Why they varied (2026-11-01).** Three causes, none of them the choices
themselves: installed by hand and alternated in one JVM, as-is and the
default are within 4% on List, and the default is 5–12% slower on Towers.

- *Order.* Definitions were decided in namespace order, so a caller was
  measured while its callees were interpreted (compiled `move-top-disk` 2x
  its interpreted time, because `push-disk` was not compiled yet). The
  investor now decides callees first (`investor/callees-first`).
- *Noise between alternatives.* Savings were compared with the
  interpreter, so between two alternatives within 10% of each other the
  faster measurement won. Within the resolution of as-is, as-is now wins:
  no guards, no premises on callees.
- *Measuring before HotSpot has compiled.* A fresh candidate of the
  investor showcase's `rank` runs at 300 µs per call, steadily, until C2
  has compiled it (half a second to a second under load), then at 20 µs.
  Two batches on that plateau agreed, so the default was sometimes
  measured at 290 µs and lost. Measuring now also waits until the JVM's
  JIT compiler has been idle for two batches (`(klara.time/compiling)`,
  L3.effect.time), bounded by two seconds.

The harness also runs each benchmark in a JVM of its own: HotSpot's
profiles of the runtime's shared code carried over between sessions (the
same List decisions measured 0.077 and 0.13 ms in consecutive sessions of
one JVM). What remains between Klara and Clojure on Towers and List is the
per-call cost of compiled code (the context fetch, the meter), not a choice.

All results agree. The interpreter is 500–1300× slower than V8; compiled
Mandelbrot is at Clojure's speed and within 1.3× of V8, the others 12–40×
behind V8. What the benchmarks taught the backend:

- **Loops must be host loops** (not self-applied functions) so the host
  keeps their locals primitive: Mandelbrot 390 → 79 ms.
- **No try at call sites.** Clojure compiles a `try` outside return position
  into a closure per evaluation; leaving compiled code is therefore a
  returned value that each let tests, not an exception.
- **Calls between compiled definitions go direct** to the host function,
  with the context fetched once per function entry.
- **Measure at steady state.** Two cold batches of a fresh candidate can
  agree; the investor warms up for 300 ms and waits until the host's JIT
  compiler is idle before trusting agreement.
- **Clojure forms are a leaky host IR.** A `loop` outside return position
  (after A-normal form, every loop in a `let` initializer) also becomes a
  closure per evaluation; Sieve's inner loop pays it per outer iteration.
  A direct bytecode backend removes this and the remaining gaps (step 3
  above): it is the next backend step.

## How we will know

Port the *Are We Fast Yet?* benchmarks (Marr, Daloze, Mössenböck, DLS 2016),
designed to compare implementations across languages: Bounce, List,
Mandelbrot, NBody, Permute, Queens, Sieve, Storage, Towers, Richards,
DeltaBlue, Json, CD, Havlak. Run each on the Klara interpreter, the JIT,
Clojure on HotSpot and JavaScript on V8 (node), and record both whether it
runs (completeness) and how fast (speed), in STATUS.md. The suite uses
mutable objects heavily; the Klara versions use atoms and records where the
originals mutate, which is itself a measurement of the programming model.

Expectation: within a small factor of V8 on numeric, interpreter/DSL and
functional code with a serious backend, ahead of it where specializers know
the domain; broad parity on object-heavy imperative code is years of
backend work.
