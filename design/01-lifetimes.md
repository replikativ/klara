# Lifetimes and bounded memory

Klara keeps old versions of programs on purpose. Without a deliberate
lifetime design that makes unbounded growth the default: every `def` creates
a world, every world could keep its predecessor, every pinned function could
keep a whole world, and every job could leave records behind. This document
states which things keep memory alive, and the obligations that make a
long-running Klara program run in bounded memory.

The first implementation relies on the JVM garbage collector. The design's
job is to make sure that the *reference graph* is right: whatever the
program no longer needs must become unreachable, promptly and without a
special cleanup pass. Collection itself is the JVM's.

## The rule

Every entity is one of two kinds:

- **Immutable values** (worlds, Code, functions, data, candidates) live as long
  as something reaches them. They are shared freely, including across forks.
- **Affine resources** (budgets, and later owned buffers or external handles)
  live for an explicit scope. They are moved or split, never copied. A fork
  cannot duplicate one.

Memory is bounded if the set of **roots** is bounded and each root reaches a
bounded amount of memory. So the design names the roots.

## Roots

Only these hold Klara memory alive (`L1.retain.roots`):

| Root | Held by | Reaches |
|---|---|---|
| Session current world | the session cell | the definitions of the current world |
| Live activations | the running machine state | their world `E`, environments, continuations |
| Values in definitions | the current world | whatever the program stored, including worlds it holds on purpose |
| Installed candidates | the definitions in the worlds that hold them (bounded per definition) | their executable and their footprint |
| In-flight jobs | the parent activation | the job's world, intents, continuation |

Everything else must be reachable only through these. In particular, the
following are **not** roots:

- **History.** A world records its parent's *id*, not the parent world. The
  session keeps a history log of `{:id :parent :changed}` summaries, bounded by
  a retention policy. Recovering an old world requires holding it: by storing
  it in a definition, in a local or in a pinned function.
- **Caches.** Analysis caches, generation lookups and per-world validity
  results are weakly keyed or bounded.
- **Discarded jobs.** Dropping a job outcome makes its world, intents and
  continuation unreachable. Only its cost survives, as a number already added
  to the parent's spent budget.

## Retention is proportional to use: footprints

Holding an old world retains every definition in it that has since changed.
That is the right behaviour for an explicitly held world value: the
programmer asked for it. It is the wrong behaviour for a function pinned to
an old world: `(world/get old 'reader)` only needs `reader` and whatever
`reader` can reach.

So a pinned function or pinned link does not hold its world. It holds a
**slice** (`L1.slice.*`): the restriction of the world to the **footprint** of
the pinned definition, meaning the definitions it transitively refers to.

- The footprint of a definition is the set of global names that occur in its
  Core term and in the bodies of functions reachable from its value, closed
  transitively in the world. It is computed on first use and cached per
  definition.
- A slice resolves every name in the footprint exactly as the world does.
  It has the world's identity, so equality and guards are unchanged.
- Slicing is only sound if every global the code can reach is named
  statically. If the footprint contains a dynamic world operation
  (`run`, `world/current`, `world/get` with a computed name), the slice is the
  whole world (`L1.slice.dynamic`).

Result: if `reader` uses only `setting`, then redefining a large `dataset`
does not keep the old `dataset` alive through `f = (world/get old 'reader)`.

## Activations are safe for space

The CEK machine follows the classic space-safety discipline
(`L0.space.*`):

- **Proper tail calls.** A call in tail position pushes no frame, so loops
  written as recursion or `loop`/`recur` run in constant control space.
- **Closures capture only their free variables.** A function value holds the
  locals its body mentions, not the whole environment in which it was
  created.
- **Frames hold only what remains to be evaluated.** A known limitation of the
  first version: a frame keeps the environment of its expression rather than
  just the variables still live after it. Trimming to live variables is a
  later refinement with the same interface.

Multi-shot continuations are values like any other: holding one retains its
frames, dropping it frees them.

## Code and candidates

- **Code** holds its lifted constants and the slices of its pinned links. Late
  links hold nothing: they are names.
- A **candidate** holds its compiled executable, its premises (name and
  generation pairs) and the constants its pinned or guarded links resolved
  to. It does not hold the world it was prepared in.
- **Generated JVM classes** are collected only when their class loader becomes
  unreachable. Each candidate is compiled in its own class loader, owned by
  the candidate, so an unreachable candidate frees its classes
  (`L4.retain.classes`).
- **Installed candidates** live on their definitions in worlds
  (`L4.exec.provenance`), a bounded number per definition
  (`L4.retain.dispatch`). A world that becomes unreachable takes its
  compiled code with it; activations still using a candidate keep it alive
  until they finish. Profiles hold samples only as bounded plain data, and
  stored candidates keep no profile annotations, so neither keeps worlds or
  arguments alive (lifetime tests).

## Jobs, intents and receipts

- A job's **intents** (deferred printing) are kept in a bounded buffer charged
  to the job. Exceeding it fails the job with `L3.job.intent-limit`.
- **Spent budget** is aggregated, not logged: each settlement adds numbers to
  the parent's counters. A detailed trace of each job is retained only when
  explicitly requested for that job (`:trace true`).
- An **exhausted** job holds its continuation in the outcome. Resuming or
  dropping the outcome are the two ways it ends.

## Making retention visible

`(klara/retained)` returns the session's roots and what they reach, as data:
current world size, history length, installed candidates per name, and live
jobs. This is how a programmer or an agent finds out what is keeping memory
alive.

## Future: charging retention

The objective is to treat retention as a resource like steps: a root that
keeps an old world or a candidate alive holds a lease charged to an owner's
budget, so a policy can decide to release it. The first version reports
retention but does not charge for it. The interface is designed so leases can
be added without changing the roots.

## Obligations and tests

Each lifetime rule has a **collectability test**: after an operation, a weak
reference to the object that should be free must clear after garbage
collection.

| Rule | Operation | Must become unreachable |
|---|---|---|
| `L1.retain.history` | redefine `x` | the previous world |
| `L1.slice.footprint` | pin `reader`, redefine unrelated `dataset` | the old `dataset` value |
| `L3.job.discard` | drop a job outcome | the job's world and continuation |
| `L4.retain.classes` | evict a candidate | its class loader |
| `L0.space.closure` | make a closure inside a scope holding a large local it doesn't use | the large local |

A **soak test** repeats redefine → job → prepare → install → evict in a loop
under a fixed heap and checks that retained heap after garbage collection
stays flat.
