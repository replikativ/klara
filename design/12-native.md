# Native substrates: how to compile Klara without being naive

Status: direction only; nothing here is built. It records how native
compilation should fit the model so that the next backend (the JVM bytecode
backend, option B in 07-performance.md) is designed with the right
interfaces. Not needed for the current papers.

## The principle

Klara's meaning is the interpreter with every check (00-model.md,
11-profiles.md). A compiled function is a refinement the kernel admits, and
it keeps one contract wherever it runs: at every point where it may leave
there is a frame state, a leave hands the interpreter a state the
interpreter would itself have reached, and steps are metered
(L4.exec.leave, L4.exec.frame-state, L4.lower.steps).

So a native backend is not a separate implementation of Klara. It is one
more substrate for the same refinement, and it needs an interpreter running
on that substrate to leave to. The interpreter is therefore not optional on
a native target: it is emitted by the same pipeline that emits compiled
code. The staged interpreter (08-staged-jit.md) is already Klara code; on a
native substrate it is compiled like any other definition.

## Three layers

1. **Klara.** Core, the staged interpreter, the compiler and investor, the
   libraries. Ordinary Klara: persistent values, multi-shot effects, jobs,
   worlds. This layer is the meaning and is written once.
2. **The low IR and machine descriptions.** A target-independent IR below
   Core: A-normal form with explicit frame states and leave points, step
   ticks, allocation sites, effect and host boundaries, and value
   representations (boxed, unboxed long and double, owned, unboxed tokens).
   Its refinement of Core is stated in the formal model. Below it, each
   target is a *machine description*: registers, instructions with their
   constraints and costs, calling conventions, the memory model and
   atomics. Machine descriptions are Klara values, versioned in worlds and
   checked like any definition; instruction selection is rewriting, the
   same checked rewriting the JIT uses (09-extensions.md). The JVM is the
   first machine; a portable bytecode machine (an interpreter on any
   substrate) the second; x86-64 and AArch64 after.
3. **Runtime services, in the affine profile.** What the interpreter and
   compiled code rely on, written in the affine subset (11-profiles.md)
   extended with unboxed primitives and raw memory, and compiled without
   a collector of its own:
   - allocation and garbage collection;
   - frames and continuation segments: capture, one-shot and multi-shot
     resumption;
   - node storage for persistent structures and worlds;
   - meters and wallets (design/10-accounting.md, with unboxed tokens);
   - the job scheduler and threads;
   - the host and foreign-function boundary (L3.effect.host-boundary).

   The interpreter is not in this layer; its affordances are. This is the
   split Scheme48 made with PreScheme, RPython makes for PyPy, Jikes RVM and
   MMTk make in Java and Rust, and Go makes for its runtime: a restricted,
   collector-free subset of the language for the parts that manage memory,
   the full language on top. The affine profile is Klara's version of that
   subset, which gives it a second purpose beyond performance.

## What to adopt from Chez Scheme (the approach, not the code)

- **Nanopass.** Many small passes between precisely defined intermediate
  languages, each checkable on its own, down to the machine descriptions.
  Klara's version adds what Chez does not have: each pass's output is an
  admitted refinement, and the frame states survive every pass.
- **The interpreter as a machine.** Chez's portable bytecode target is
  defined like any other machine and is how new platforms are bootstrapped.
  Klara's portable machine plays the same role: the interpreter on a
  substrate we have no native description for yet.
- **Segmented stacks for first-class continuations** (Hieb, Dybvig and
  Bruggeman, *Representing Control in the Presence of First-Class
  Continuations*, PLDI 1990): capture splits the stack into segments, and
  multi-shot resumption copies a segment lazily. Klara's continuations are
  multi-shot and resumed by handlers (L3.cont.multishot), so this is the
  representation to start from.
- **Self-hosting through boot images**: the compiler compiles itself, and
  the boot image is an artifact of a world, not a trusted seed.

## What metacarp contributes

metacarp (../metacarp) is a self-hosting compiler for Carp, written in Carp,
with ownership and borrow checking, specialization, and C emission. Carp's
model (no collector, ownership) is close to the affine profile, and C is a
portable early target for the runtime layer. Its ownership and
specialization passes are prior art for the runtime layer's checks; a
Klara-to-C path through the affine profile could reuse its experience
before Klara has its own machine descriptions.

## Garbage collection with Klara's memory model

A top-tier collector is a project of its own. Klara's memory model
(01-lifetimes.md) makes the problem easier than for a general language:

- **Immutability.** Persistent values only point to older values, so
  old-to-young pointers arise only through mutable cells (atoms, volatiles,
  arrays, transients). The write barrier belongs on those alone.
- **Precise roots.** The roots are named (L1.retain.roots), and the frame
  states compiled code already records give precise stack maps.
- **Regions for free.** A job is a natural region: its world, intents and
  young objects become unreachable when its outcome is discarded, and
  owned values never leave the compiled region that owns them
  (04-ownership.md).
- **Retention is accounted.** Footprints and retention reporting
  (01-lifetimes.md) make what is kept visible; charging retention later is
  an accounting question (design/10-accounting.md).

The pragmatic first collector is MMTk (Immix and generational plans,
requiring precise roots, which Klara has) behind the runtime layer's
allocation interface; a collector written in affine Klara can replace it
behind the same interface.

## Hosting

The JVM is one host; a native substrate is another, with its own host
functions and the same boundary rule (L3.effect.host-boundary). Clojure
compatibility (03-clojure.md) stays a property of the Klara layer, not of a
host.

## Order (not now)

1. The JVM bytecode backend (option B), designed around the low IR and a
   machine-description interface, the JVM as the first machine; unboxed
   tokens and owned collections there (P11's open items).
2. The low IR's refinement of Core stated in the formal model, in a calculus
   of its own as λ-acct is.
3. The portable bytecode machine: the interpreter emitted for any substrate.
4. x86-64 and AArch64 machine descriptions.
5. The runtime layer in affine Klara: allocation over MMTk, segmented
   stacks, scheduler; then a collector of our own.
6. Self-hosting: the compiler and runtime compile themselves into a boot
   image held by a world.

Only step 1 is on the agenda; the rest is why its interfaces matter.

## Open questions

- Which unboxed and raw-memory primitives the runtime layer needs, and how
  the affine judgment checks them (pointers as tokens, regions as wallets?).
- How much of the low IR the kernel checks itself and how much is checked
  by translation validation (L4.check.certificate) per pass.
- Whether machine descriptions can be learned or tuned by the investor
  (instruction costs measured, as alternatives are today).
- How durable worlds (Datahike, yggdrasil) and a native store meet.
