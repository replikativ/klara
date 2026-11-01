# Speculation: facts, guards, frame states and a staged JIT

Status: design for the current iteration. It settles four decisions:

1. how compiled code leaves to the interpreter (frame states);
2. where static knowledge comes from (facts from pluggable type systems);
3. how the JIT is built (a stage-polymorphic interpreter written in Klara);
4. how the interpreter observes programs (profiles in prepared nodes).

The interpreter and the checker stay fixed. Everything that adapts programs
is Klara code.

## 1. Frame states: compiled code can always return to the interpreter

The machine's state is data: a node to evaluate, an environment, and a
continuation of frames. So leaving compiled code means building a machine
state and continuing from it.

Every point where compiled code may leave records a **frame state**:

```text
frame-state = [virtual-frame ...]          innermost first
virtual-frame = {:node   n                 the reference node to continue at
                 :slots  [local ...]       compiled locals filling the environment
                 :frame  kind}             the continuation frame it stands for
```

With inlining, one compiled frame stands for several machine frames, so a
frame state is a short stack of virtual frames, as in V8's deoptimizer.
Leaving points are:

- a **guard** whose condition fails (speculation, below);
- a **call** to code that may perform an effect: rebuild the state, let the
  machine perform it and capture the continuation, so multi-shot
  continuations work across compiled code;
- a **budget** check that runs out: the job suspends with the rebuilt state.

The inverse mapping enters compiled code from a machine state, which is
on-stack replacement for loops.

**The obligation** (specified as `L4.exec.frame-state`, proved for the
formal fragment): a frame state rebuilt at a leaving point is a state the
reference reaches from the same input and world.

**Stack traces** come from the same data. Prepared nodes keep the source
position of their form; the continuation is a real stack; a Klara error
carries Klara frames, rendered as `StackTraceElement`s on the JVM (and as
source-mapped frames on other hosts). Compiled code emits line numbers that
point at Klara source.

## 2. Speculation is an `if` whose else branch is the reference

A speculative candidate has the shape

```clojure
(if (guard args) specialized reference)
```

anywhere in its body, not only at entry. This makes speculation checkable
with the rules we have: the candidate is equivalent to the reference if
`specialized` is equivalent to `reference` *assuming the guard*, which for
type and shape speculation is usually definitional (the specialized branch
differs only in representation hints). Lowering then chooses how to run the
else branch: it does not compile the reference again, it leaves through a
frame state into the interpreter at that point. Deoptimization is a lowering
of `if`, not a separate mechanism.

Guards have three sources, distinguished by their evidence:

| Guard | Comes from | Example |
|---|---|---|
| world premise | unfolding a late definition | `(power, 40)` |
| speculative | a profile | `x` has always been a long |
| assumed | a certificate's hypothesis | `|x| ≤ 2^20` for Horner |

## 3. Facts: static knowledge from pluggable type systems

Core is untyped. Type systems sit on top and produce **facts**: claims about
terms with their source.

```clojure
{:term <code> :claim [:returns :long] :evidence :proved :by :ansatz}
```

| Source | Evidence | Can discharge a guard? |
|---|---|---|
| ansatz | proved (about the formal semantics; partial correctness needs no termination) | yes |
| Typed Clojure or a Klara type system | trusted by that checker | if the policy accepts the checker |
| the purity / uniqueness analyses | checked judgment | yes, for the rules that need it |
| profiles | speculative | never; they become guards |

**Discharging a guard** is a property of a call site: if facts at the caller
establish the callee's guard (a literal argument; the result of checked long
arithmetic is a long), the call goes to the guard-free entry. AOT is the
limit where every guard is discharged or deliberately kept with its
interpreter fallback.

Facts also **widen the checker**. Pure and total code admits more equivalence
rules: dead code elimination, let floating, common subexpression
elimination, earlier placement of shared code. Each such rule has a
precondition (pure, total) and is proved once for the formal fragment.

## 4. The JIT is a stage-polymorphic interpreter written in Klara

Instead of Truffle's automatic partial evaluation, Klara follows the staging
route (Amin and Rompf, *Collapsing Towers of Interpreters*, POPL 2018;
Rompf's Lightweight Modular Staging): one interpreter for Core, written in
Klara, that either evaluates a term or, given static knowledge, generates
its residual code with `code` and `esc`.

```text
interpret : node × env → value                 run directly (testing, the reference shape)
generate  : node × static-env × profile → Code  run staged: the JIT
```

- What is static: the program, constants, monomorphic call targets and types
  from profiles, facts. What is dynamic: everything else.
- At a speculation the generator emits `(if guard <specialized> <reference>)`
  (section 2). It knows its own state at that point, so it emits the frame
  state too: frame states fall out of the staged interpreter rather than
  being reconstructed by a separate compiler.
- The residual is ordinary Code. The checker relates it to the reference;
  the backend lowers it; HotSpot does register allocation and machine code.
- Because the JIT is a Klara program, it can be read, tested and improved by
  the same mechanisms it serves, and its residuals can be verified.

The host prepared-node interpreter remains T0. Cheap host improvements (node
specialization from profiles, closure compilation of flat pure subterms)
speed up T0 without changing the architecture.

## 5. Profiles: feedback in prepared nodes

As in Truffle, each prepared node holds its own feedback, written by the host
interpreter and read by Klara as data:

- call nodes: argument type classes, call target identity, call counts;
- `if` nodes: branch counts;
- global nodes: definitions seen;
- collection operations: shapes (vector length ranges, map key sets).

`(klara.profile/snapshot f)` returns the profile of a function's nodes as a
value. Profiles can be stored in worlds and saved with builds, so an AOT
preparation can use the profile of an earlier run.

## 6. Specializers: the JIT is programmable

What the JIT does to a function is decided by a **specializer**: a pure Klara
function called at compile time with a context, returning Code or declining.

```clojure
(defn match-specializer [ctx default]
  (let [pattern (profile/stable-arg ctx 0)]          ; argument 0 always the same value?
    (if pattern
      (jit/guard (code (same? (esc (jit/arg ctx 0)) (esc (lift pattern))))
                 (stage-matcher pattern (jit/arg ctx 1)))   ; our own code for that pattern
      (default ctx))))

(defn ^{:klara/specialize match-specializer} match [pattern s] ...)
```

| Context field | Contents |
|---|---|
| `:reference` | the function's Code, with its links |
| `:profile` | argument classes, stable values, call targets, branch counts, shapes |
| `:facts` | what type systems and analyses established |
| `:runtime` | host and hardware data: JVM, cores, measured call and allocation costs |
| `:budget` | what this specialization may still spend |

`jit/guard` builds `(if guard specialized reference)` with its frame state;
`jit/arg` gives the arguments as Code; representation hints mark unboxed
values. Specializers compose like middleware: each receives the default and
handles what it knows. The JIT's own strategy (section 4) is the default
specializer, written against the same interface.

A specializer runs inside the investor's job: in a fork, under a budget, with
its cost charged, unable to publish or perform effects. Its output is checked
like any candidate. Anything it learns that is worth keeping (a tile size
for this machine) is returned as data and stored in a world by the investor.

## 7. The investor

Choosing what to specialize is an investment ([05-specialization.md](05-specialization.md)):
a Klara policy compares expected benefit (calls times predicted saving, from
profiles) with preparation cost (generation, checking, proof search,
lowering; measured) and risk (guard miss rates). It may explore alternatives
in parallel forked jobs, settles once, and pays for everything it tried. It
starts as a threshold and a cost table; the interface is ready for learned
policies.

## What this iteration delivers

See [PLAN.md](PLAN.md).

See [PLAN.md](PLAN.md) for the order of work and the showcase programs that
validate each decision.
