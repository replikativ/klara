# The Klara programming model

Klara is a Clojure dialect in which a running program can keep several
versions of itself, construct new code, try changes in isolation, and adopt
an optimized implementation only after it has been checked against the
program it replaces.

This document is the entry point to the design. It names every concept the
language exposes and the operations between them. The other design documents
refine one aspect each:

| Document | Question it answers |
|---|---|
| [01-lifetimes.md](01-lifetimes.md) | What keeps memory alive, and how do we stay in bounded memory? |
| [02-compilation.md](02-compilation.md) | How does code become a checked, installed executable? |
| [03-clojure.md](03-clojure.md) | How does Klara relate to Clojure code, tools and agents? |
| [04-ownership.md](04-ownership.md) | How do affine regions become checked staged rewrites? |
| [05-specialization.md](05-specialization.md) | Candidates, evidence, the investor, facts, JIT to AOT |
| [06-speculation.md](06-speculation.md) | Frame states, speculation, pluggable type systems, the staged JIT, profiles |
| [07-performance.md](07-performance.md) | How fast is it, measured, and where can the design go? |
| [08-staged-jit.md](08-staged-jit.md) | The staged interpreter as the default specializer |
| [09-extensions.md](09-extensions.md) | Rules, effect classes and vectorization: extending the JIT |
| [PLAN.md](PLAN.md) | The phases of this iteration and what each delivered |
| [related-work.md](related-work.md) | Where the ideas come from and what is new |

The normative rules are in [`spec/`](../spec/README.md); each rule has an ID
such as `L2.run.closed` that error messages, code comments and tests cite.

## The value proposition in one program

```clojure
(ns demo.power
  (:require [klara.stage :refer [code esc]]
            [klara.compiler :as compiler]))

;; An ordinary definition: the meaning.
(defn power [n x]
  (if (= n 0) 1 (* x (power (dec n) x))))

;; A staged generator: a program that writes a program.
(defn power-gen [n x]
  (if (= n 0)
    (code 1)
    (code (* (esc x) (esc (power-gen (dec n) x))))))

;; Use the generator as an optimizer for (power 3 _), checked against power.
(def cube
  (compiler/executable
    (compiler/prepare (code (fn [x] (power 3 x)))
                      {:recipe (fn [_reference] (code (fn [x] (esc (power-gen 3 (code x))))))})))

(cube 3) ;; => 27, through compiled code that the checker accepted
```

Three things happen that ordinary Clojure cannot express:

1. `power-gen` produces **code as a value**, which can be inspected, stored
   and run (staging, layer L2).
2. `compiler/prepare` runs the recipe in an **isolated job with a budget** and
   accepts its output only if a small trusted checker shows it means the
   same as the reference `(fn [x] (power 3 x))` (layers L3, L4).
3. If `power` is later redefined, `cube` notices that its premise no longer
   holds and falls back to the reference meaning, which now calls the new
   `power` (worlds, layer L1).

## Layers

Each layer depends only on the layers above it in this table. Each has a
design section here, a spec file, a source directory section, examples and
tests.

| Layer | Concepts | Spec |
|---|---|---|
| L0 Core | values, Core terms, the CEK machine, Clojure surface | [spec/L0-core.md](../spec/L0-core.md) |
| L1 Worlds | worlds, definitions, generations, modules, sessions | [spec/L1-worlds.md](../spec/L1-worlds.md) |
| L2 Staging | Code, links, `code` `esc` `lift` `run` `reify` | [spec/L2-staging.md](../spec/L2-staging.md) |
| L3 Effects and jobs | `perform`, handlers, continuations, jobs, budgets | [spec/L3-effects.md](../spec/L3-effects.md) |
| L4 Compilation | reference, recipe, checker, candidate, install, fallback | [spec/L4-compiler.md](../spec/L4-compiler.md) |
| L5 Guest compiler library | policies and recipes written in Klara | `lib/klara/` |

## The nouns

Klara has six kinds of things a programmer handles. Everything else is
ordinary Clojure data.

| Noun | What it is | Printed as |
|---|---|---|
| **Value** | Immutable Clojure data, functions, and the nouns below | as in Clojure |
| **World** | An immutable map from qualified names to definitions | `#klara/world w12` |
| **Code** | A program fragment whose global names carry an explicit link | `#klara/code (fn [x__1] (* x__1 x__1))` |
| **Continuation** | The rest of a computation, captured by an effect handler | `#klara/cont[...]` |
| **Job** | The outcome of running a computation in an isolated world under a budget | a map `{:status ...}` |
| **Candidate** | A checked executable together with the premises under which it is valid | `#klara/executable[demo.power/power]` |

There is no separate "program" type. A reference to a definition in a
particular world is Code with a pinned link (below), and a compiled function
is an ordinary callable value backed by a candidate.

## Worlds and activations (L1)

A **world** maps names such as `demo.score/score` to **definitions**. A
definition records its source form, its Core term, its value and a
**generation**: a number that changes whenever the definition is
re-evaluated. Worlds are immutable values; `def` produces a new world.

A **session** (a REPL, a loaded program, a test) holds a mutable reference to
its *current* world, the only mutable cell in the model. Publishing a world
updates it atomically.

An **activation** is one top-level evaluation (a REPL input, a file form, a
call from the host). It runs against a fixed world, chosen when it starts.
Redefinitions published by *other* activations while it runs do not change
the meaning of the code it is running. Its world changes only at explicit
points: its own `def` (it reads its own writes, so loading a file form by
form works as in Clojure) and `(world/advance)`, which moves it to the
session's latest world. This gives compiled code a stable world for its whole
duration, so validity checks happen at entry rather than on every global
access.

```clojure
(def setting 10)
(defn reader [] setting)
(def old (world/current))          ; a world value; holding it retains it
(def setting 20)

(reader)                            ; => 20, the current world
(world/in old reader)               ; => 10, call reader with old as its world
(def f (world/get old 'reader))     ; f is pinned to old
(f)                                 ; => 10 wherever it is called
```

**The context rule** (`L1.context.*`). Every activation has an *effective
world* `E` and a *mint* `m`, which is either `nil` or a world.

- Top-level activations start with `E` = the session's current world, `m` = `nil`.
- A global name in executing code resolves in `E`.
- A function created while running stamps `m` as its **basis**. Functions
  defined at top level therefore have no basis: they are *open*, and run in
  the world of whoever calls them. That is Clojure's late binding, and it is
  what makes redefinition at the REPL work.
- Calling an open function keeps the caller's `E` and `m`. Calling a function
  with basis `w` runs its body with `E = m = w`.
- `(world/in w f & args)` calls `f` with `E = m = w`. `(world/get w 'x)`
  returns the value of `x` in `w`, pinned to `w` if it is a function.

This rule is the prototype's, made explicit. Open functions give Clojure's
late binding; basis-stamped functions give values that remember their world.

## Code and links (L2)

**Code** is a Core term (L0) used as data. Local variables in Code have
unique names, so splicing never captures. Global names do not stand alone:
each carries a **link** that says which world gives it meaning.

| Link | Written | Meaning | Compiler treatment |
|---|---|---|---|
| late | `demo.score/adjustment` | resolve in the effective world where the code runs | a lookup at run time |
| pinned | `(klara/at w12 demo.score/adjustment)` | resolve in world `w12`, always | a constant: inline and fold freely |
| guarded | `(klara/guarded w12 demo.score/adjustment 7)` | the value at generation 7, while the running world still has generation 7 there; otherwise late | a constant plus a check at region entry |

A guarded link means the same as a late link (`L2.link.guarded`). It only
records an assumption the compiler made. So there are two semantic link
kinds and one implementation device.

**The staging operations:**

| Operation | Effect |
|---|---|
| `(code e)` | Build Code for `e` without running it. Globals in `e` become late links. Present-stage locals used inside `e` are lifted. |
| `(esc g)` | Inside `code`: run the generator `g` now; it must return Code, which is spliced in. |
| `(lift v)` | Code that evaluates to the present value `v`. Allowed for immutable data, functions, worlds and Code. Mutable host objects are rejected. |
| `(run c)` | Evaluate closed Code in the current context. `run` is evaluation, not compilation. |
| `(reify f)` | Code whose structure is the function `f`: its parameters, its body with links, and its captured values lifted. An open function gets late links; a function with basis `w` gets links pinned to `w`. |
| `(world/link w 'x)` | Code consisting of the pinned link to `x` in `w`. |

Two laws tie these together (`L2.lift.preserves`, `L2.reify.preserves`):

```text
(run (lift v))   behaves as v   in every world
(run (reify f))  behaves as f   in every world
```

The second law is the one that needs links. Without pinned links, reifying a
function pinned to an old world produces code that reads the *new* world,
which silently changes the function. The prototype first did exactly that,
then rejected the operation. Links make it correct.

**Stages are relative.** A definition has no stage number. "Stage" means
nesting depth of `code` within one expression: inside `code` we are one
stage later, inside `esc` one stage earlier. The same helper function can be
called by a generator at stage 0 and appear in generated code at stage 1.
Cross-*world* meaning is carried by links, not by stage numbers.

## Effects, handlers and jobs (L3)

An **effect** is a request to the context: `(perform :io/print "hi")`. A
**handler** decides what it means:

```clojure
(handle {:io/print (fn [k msg] (k nil))}   ; swallow printing
  (println "never shown")
  42)
;; => 42
```

A handler receives the **continuation** `k`, an ordinary function that
resumes the computation. Calling `k` twice is allowed (multi-shot). If the
resumed computation uses an account token (below) that the first resumption
already consumed, that use is an error (`L3.affine.reuse`). Resuming runs
with the resumer's budget and wallet, never captured ones
(L3.cont.context): continuations copy control, not authority. Unhandled effects reach the session's
default handlers, so `println` prints.

A **job** runs a computation in a fork of the current world, under a budget,
and returns its outcome as data instead of changing anything:

```clojure
(def outcome
  (job/run {:budget {:steps 10000}}
    (fn []
      (def setting 99)        ; changes the job's world only
      (println "in a fork")   ; deferred: recorded, not printed
      (reader))))
;; => {:status :done, :value 99, :world #klara/world w14,
;;     :intents [[:io/print "in a fork"]], :spent {:steps 41}}

(job/adopt! outcome)          ; publish w14's changes, then print
```

- Statuses: `:done`, `:failed` (with the error), `:exhausted` (with a
  continuation that `job/resume` can continue under a new budget).
- Discarding a job is doing nothing with its outcome. Its **cost is not
  refunded**: the steps it consumed are charged to the parent's budget
  whether or not the result is adopted.
- Inside a job, printing becomes a recorded intent, `def` changes only the
  job's world, and `swap!`, `reset!`, `vswap!` and the like on atoms and
  volatiles created outside the job are refused (`L3.job.host-mutation`). Interop and
  array writes on outside objects are not refused yet: a job isolates code
  that avoids them. The first version supports exactly these effects in
  isolation: pure computation, world changes, printing, and budgets.

**Affine resources.** A budget is a resource: it can be split and moved but
not copied. Reserving steps for a job moves them out of the parent's budget,
and unused steps return when the job settles (L3.budget.nesting). Budgets of
any resource (money, time, connections, permissions with k holders), and
tokens that pass the right to spend or hold explicitly to callees, are
designed in [10-accounting.md](10-accounting.md).

**Authority and erasure.** The meaning of a program is what the machine
does, with every check: misused authority is a named error where it is
used, and conservation (minted = held + live + spent) holds for every
program. Static judgments never change that meaning; they let the compiler
drop a check or change a representation, each with an erasure theorem. A
raise leaves the tokens it skips live until their job settles; a job
outcome is resumed and adopted at most once; continuations stay multi-shot,
and declared code holds no token where one may be captured.
[11-profiles.md](11-profiles.md) states the rules, the Rust mapping, and
the accounting calculus λ-acct in which conservation and affine soundness
are proved.

## Compilation (L4)

Compilation is a staged program that runs in a job, with roles separated by
authority:

| Role | Written by | Trusted? | Does |
|---|---|---|---|
| Reference | the programmer | defines meaning | ordinary Code, usually with late links |
| Recipe | anyone (guest Klara) | no | proposes candidate Code, for example by running a generator |
| Policy | anyone (guest Klara) | no | decides when to prepare, with which recipe and budget |
| Checker | the runtime | yes, small | accepts the candidate only if it is equivalent to the reference |
| Backend | the runtime | yes | lowers checked Code to JVM bytecode |
| Runtime | the runtime | yes | installs candidates, checks premises at entry, falls back |

The checker decides equivalence by definitional unfolding, the way a proof
assistant's kernel compares terms: it may replace a link by its definition,
substitute values for parameters, choose a branch of an `if` on a constant,
and evaluate a primitive on constant arguments. Each rule preserves meaning
under Clojure's evaluation order, failures and effects. It does not apply
algebra: `(* x 1)` and `x` are different programs, because `(* "a" 1)`
throws. Unfolding a late link records a **premise** (the generation it saw),
which becomes a guard checked at entry to the compiled code.

```text
prepare(reference, recipe, budget)  ->  job outcome with candidate | rejection | exhaustion
executable(candidate)               ->  callable: premises hold in E ? compiled body : reference
install!(candidate, name)           ->  calls to name in a world where premises hold use it
pin(code, w)                        ->  same code with every late link pinned to w (AOT)
```

**AOT is a special case.** Pinning a program to a release world makes every
link a constant. The checker then records no premises, the compiled code has
no guards, and nothing can invalidate it. The same pipeline gives JIT-style
guarded code for live worlds and static code for releases.

See [02-compilation.md](02-compilation.md).

## Who may change what

The authority structure keeps self-modification safe without restricting
who writes generators or policies:

- Any code may build Code, run it, start jobs and propose candidates.
- Publishing a world changes the session's current world, and goes through
  `world/publish!` or `job/adopt!`.
- Installing a candidate changes how calls are executed, never what they
  mean; it requires a candidate that the checker accepted.
- Changing the checker or backend is changing the trusted base. It is not a
  language operation.

## Two ways to use Klara

Klara is designed to be used by people and by AI agents of varying skill:

- **Forms** (`code`, `esc`, `handle`, `world/in`) for programmers who want to
  write generators and handlers directly.
- **Plain functions returning data** (`compiler/specialize`,
  `compiler/optimize!`, `job/run`, `klara/explain`) for everyone else. An
  agent can call them like tools and read the resulting maps. Every outcome
  is printable data with a `:status` and, on failure, a `:rule` naming the
  spec rule that applied.

See [03-clojure.md](03-clojure.md).
