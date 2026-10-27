# Klara Core v2 — second design iteration (2026-10-27)

Revises `01-core-v1.md` after the worked examples (`02-examples.md`), the
spindel/sci alignment (`03-spindel-alignment.md`), research notes F and G, the
two Codex reviews (`reviews/codex-astra-critic.md`,
`reviews/codex-challenge-2.md`) and experiment X1. v1 stays as the record of
the first synthesis; its decision log (§11–13) remains valid unless revised
here. Pending: the JVM handler cost probe (`klara-proto/handlers`) and X2
(`klara-proto/kmap`) will fix the numbers in §4 and §8.

**v1 promise (adopted from the Codex review):** *a forkable, inspectable
execution environment for simulation, inference and certified optimization,
embedded in the Clojure ecosystem.*

## 0. What changed from v1

| v1 | v2 | Why |
|---|---|---|
| Non-copyable objects enforced by dynamic sort tags | **Authority**: aliasable data, non-duplicable capabilities to consume, branch and settle | `(let [r (open …)] [r r])` copies without a copy operation (Codex §1); spindel's affine settlement already works this way |
| One identity for functions (hash of source) | **Three identities**: code, closure, executable | `(make-adder 1)` vs `(make-adder 2)` (Codex §1) |
| Finite discrete subdistributions | **Weighted execution trees with limits**, normalization separate | recursion gives countable support; `factor 2` gives mass > 1 (Codex §1, Staton et al.) |
| "Annotations never change meaning" | **Three contracts**: hints, checked claims, approximation | caught blame and threshold branches break the single statement (Codex §3) |
| `converge` in the core | **Experimental library** yielding (value, certificate-or-estimate) | a residual bounds error only under contraction; predictions never certify (Codex §3) |
| Dynamic deep handlers only | **Lexical handler instances** for user effects, dynamic handlers for ambient effects | accidental handling without a type system; makes dispatch erasure the common case (G) |
| Fork = copy for values | **Snapshot fork** (pinned parent root); following is `fork-following` | Q4, spindel alignment |
| No rule for external effects in forks | **Reversible / irreversible effects**, deferred intents | G10; spindel and sci both lack it |
| Expansion invalidation designed from scratch | **One tracking engine** (spindel's), code dependencies included | X1 rebuilt spindel's `track`; X6 tests the merge |
| "Never worse than Clojure" as a slogan | **Release gates R1–R8** for a stated fragment | Codex challenge §3 |
| `defop` dispatch for all abstractions | **Algebras as values** (monoid, join, distance, measure); `defop` for canonical structure | a type has several monoids (F) |

## 1. Core calculus (unchanged in shape)

Twelve forms, call-by-value, de Bruijn locals: local, `quote`, `fn`,
application, `let`, `if`, `letrec`, `resolve`, `prim`, `perform`, `handle`,
`specialize` (v1 §1). Changes:

- `handle` installs a **lexical handler instance**: `perform` names the
  instance it targets (a capability value in scope) rather than searching the
  dynamic stack. Ambient effects (`:world/*`, `:host/*`, `:time`, `:exn`) are
  handled dynamically by the outermost handlers. (G §3)
- Self tail calls in `letrec`/`loop` positions run in constant space (a spec
  obligation; the JVM lacks general tail calls). (02-examples §3)
- `quote` is datum quotation. Syntax objects (with scope sets) and code values
  are separate value kinds (§6). (Codex §4)

## 2. Authority, forks and effects

**Data is aliasable; authority is not.** Every value may be referenced any
number of times. What cannot be duplicated is an *authority*: the capability
to consume a resource, branch or settle a branchable system, spend evidence,
or spend budget. Authorities are tokens with a lifecycle (open → advancing →
settled | incomplete), taken from spindel's `ForkHandle` (#41) and
`partition-fork!` (#43).

| Authority over | Operations | Split rule |
|---|---|---|
| resource (file, channel, Java object, array) | consume, close | none; transfer only |
| branchable system (world, datahike, yggdrasil, hosted atom) | `branch!`, merge, discard, transfer, partition | partition: disjoint and exhaustive, consumes the parent |
| evidence (an observation's likelihood) | fit, hold out, spend | split preserving mass; population join-then-split for resampling (G1) |
| budget (time, memory, money, energy) | spend | split at forks; hard components (memory, deadlines) vs traded (money, energy) (Q15) |
| randomness (splittable key) | draw | split by default; shared only in a `:coupled` fork (Q6) |

- **Fork** = snapshot of the world (overlay over the pinned parent root) plus
  a split of every authority the forked computation holds. A fork that would
  need to duplicate an authority is rejected.
- **Effects are reversible or irreversible.** Reversible effects act on
  branchable systems inside the branch. Irreversible effects (host I/O) are
  *deferred* inside a fork: queued as intents with the branch, executed on
  adoption, dropped on discard. Performing one directly needs an explicit
  capability, recorded in the receipt. (G10)
- **Settlement** happens exactly once per authority, fails closed, and leaves
  `:incomplete` after a partial durable mutation (spindel S8–S10).
- **Multi-shot resumption** = *fork-resume*: branch the captured store and
  split authorities; implemented by resuming CPS continuations in compiled
  regions and by replay from a savepoint (spindel rebuild, foerster MCMC)
  behind opaque host frames — never by cloning host frames. (Codex §2, §4)

Dynamic checking enforces authority conservation in the core; the affine
narrowing layer proves it statically and erases checks.

## 3. Identity

- **CodeId**: hash of the α-canonical expanded syntax, frozen before
  optimization.
- **Closure**: CodeId + captured values + a global-resolution policy
  (creation basis or caller basis — default: creation basis, because a closure
  is a value). Closures holding authorities have no structural equality.
- **Executable**: a specialization of a closure: CodeId + guards + origin id.
  Executables are caches; deleting them changes no observation (gate R3).
- Values have no observable identity; `identical?` is a hint. Iteration order
  of unordered collections is unspecified in the spec and equal to Clojure's
  in compat mode (randomized only in a test mode).

## 4. Effects on the JVM: execution strategy

Decided by research note G and the Codex review; numbers pending from the
handler probe.

1. **Tail-resumptive and abortive operations** (state, reader, logging,
   `observe`/`factor` accumulating a weight, exceptions) compile to direct
   calls on the handler instance — no continuation.
2. **Dispatch erasure by staging**: when the handler context of a region is
   known at specialization time (grade S, or A with a guard), the region is
   specialized per handler context and every `perform` becomes a direct call.
   The guard is checked **on region entry**; live JVM frames cannot be
   converted to a continuation afterwards, so the fallback is replay from the
   region entry. This is Effekt's capability-passing result (ICFP 2020)
   reached by staging instead of types.
3. **Resumptive regions** use selective CPS (partial-cps) or explicit heap
   frames; host frames in between (Klara → linked Clojure → Klara callback →
   effect) are an opaque boundary and a tested error, not a promise.
4. **Multi-shot** = fork-resume: CPS-compiled regions resume their captured
   continuation directly (measured 1.65× a hand-written search for exact
   enumeration); replay from a savepoint is the fallback for regions behind
   opaque host frames (15× on enumeration, 4.6× slower than CPS on SMC).

**Measured (handler probe, `klara-proto/handlers`, OpenJDK 25 C2, noisy
machine — read ratios):** tail-resumptive fast path 1.18× a protocol call
(while a site sees ≤2 clause types; 7.7× at 3); unused handler frame ≈ free,
installing one ≈11 ns; CPS taints code 2.7× even when no perform fires (so CPS
regions must be narrow — dispatch erasure matters); one-shot via CPS ≈12 ns
per perform; Loom `Continuation` 250 ns per perform and one-shot only
(rejected); preallocated stackless exceptions 50× cheaper than `ex-info` for
aborts. Consequence: operations are classified tail / abort / general **at
definition time**, because CPS compilation must be decided when the
performing code is compiled; `choose` gets a direct version for
importance sampling, where it is tail-resumptive.

## 5. Probability semantics

Weighted execution trees with nonnegative weights; recursive programs denote
increasing limits (countable support, possibly infinite total mass);
normalization is a separate operation with explicit zero- and infinite-mass
failure (Staton et al. 2016). Observations distinguish returned values,
language errors, divergence and external traces. Handler order is part of a
program's meaning and is fixed explicitly. Adequacy A1 is stated for a named
fragment first (bounded, terminating, discrete), then extended.

## 6. Staging, syntax extensions, code values

- Value kinds: datum (`quote`), syntax (scope sets), open code, closed code.
  `run`/`eval` accepts only closed code; closing is a checked operation with
  dynamic scope-extrusion checks (BER MetaOCaml); `lift` refuses values that
  hold authorities.
- **Syntax extensions** declare an input grammar and binding interface and
  receive an expansion-context capability (local expansion, controlled
  intentional capture). **Staged functions** build code with brackets and run
  it through `close`/`run`. Typed staging is an opt-in layer on the same
  runtime checks. (v1 §13, Codex §4)
- Macros are pure by default; effects through an explicit opt-in, recorded by
  the expansion handler as versioned inputs; volatile inputs disable cache
  reuse. Negative lookups are dependencies. (Q8, Codex §4, X1)
- Expansion and specialization share one tracking engine with two visibility
  rules (new world after basis raise vs transparent swap). The engine is
  spindel's (X6 decides the merge). Re-expansion runs as an explicit,
  cancellable **expansion transaction** with a visible pending state; an old
  expansion never runs while claiming the new basis. (Codex challenge §3)
- Specialization is a cache with guards, **never on the critical path of a
  redefinition**; swaps happen at function entry or declared state-transfer
  boundaries only.

## 7. The three contracts

1. **Hints** (`:hint`): erasure preserves observable behaviour including effect
   traces; fallback never repeats a performed effect.
2. **Checked claims** (default for annotations): successful execution equals
   the unannotated result; added precision may only add designated check
   failures. The guarantee excludes contexts that catch blame errors, or
   relates them explicitly. Shallow checks license only shallow
   representations; deep representation changes need guarded projections or
   element validation and must preserve overflow, equality, hashing and
   exceptions.
3. **Approximation** (`within`): an explicit boundary with a metric and an
   observation contract; behaviour outside it is exact. Guarantees are
   labelled *certified bound*, *statistical bound* (with assumptions and
   failure probability) or *estimate*; estimates never satisfy a hard
   tolerance.

Laws that license optimizations: proved in ansatz → may remove guards;
property-tested → only guarded optimizations with fallback, blame on the
instance owner; documented only → never. (F)

## 8. Standard library and evaluation

- **Algebras as values** (passed like reducing functions): Monoid, Join (a
  commutative monoid classified by divisibility, per the ESOP paper), Distance
  (for `within`), Measure (choose/observe), spindel's delta algebras,
  Foldable/transducers. `defop` dispatch for canonical structure (`=`,
  `compare`, extractors). (F)
- **Pattern matching**: open by design (extractors through `defop`, open map
  patterns by key, exhaustiveness only for sealed tags) — this answers Rich
  Hickey's actual objection (closedness and positional coupling); decision
  tree vs backtracking is a per-site realization choice. (F)
- **Laziness**: `map` & co. stay lazy (naming rule). A lazy seq realized
  before a fork is shared; each fork realizes its own tail. Klara's
  `lazy-seq` rethrows a cached failure (Clojure returns NPE/`[]`/truncated
  data after a failed realization — a divergence surfaced as an error, allowed
  by the naming rule). Effectful seqs are resources. Generators and streams
  are a `yield` effect with a handler. (F)
- **Async** = `perform` with one-shot continuations; no function colouring.

## 9. Interop, compatibility, hosting

Compatibility levels: **L0** linked (everything runs, outside fork
guarantees), **L1** hosted (unmodified, forkable; starts as forkable sci plus
Klara's expander), **L2** Klara-idiomatic. Naming rule: same name ⇒ same
behaviour on non-failing programs; different behaviour ⇒ different name or an
error. Klara types are real JVM classes implementing Clojure's interfaces
(map: `IPersistentMap` + `MapEquivalence` + `java.util.Map`); var caching
through watches is incomplete (`unbindRoot` bypasses watches) and keeps a
root/version check. Shapes are logical ids with immutable schema versions and
explicit migrations; specialized field access guards the exact layout.
(D, Codex challenge §3)

## 10. Release gates (Codex challenge §3), for a stated fragment

Fragment: ordinary function and dispatch edits, unchanged host ABI, bounded
expansion, no requested migration, optimizer optional; baseline Clojure with
direct linking off, same JVM and machine.

R1 publication work independent of specialization count and dependent fanout ·
R2 first correct result ≤ Clojure + max(5 ms, 10 %) at p99 · R3 deleting all
caches preserves results and effect traces · R4 old/new versions coexist
across pinned fibers and forks · R5 bounded cache cost; churning sites go
generic · R6 memory plateaus after 10,000 edits · R7 shape continuity without
restart · R8 expansion honesty.

## 11. Prerequisites found by the reviews

- **ansatz `check-constant-replace`** replaces a constant without rechecking
  dependents (inspection; to reproduce). Certificates are untrusted until
  proof environments use fresh internal names and immutable roots.
- **v0 dispatch firewall** keeps a stale implementation when a method is
  replaced at the same pattern (inspection; to reproduce).
- **v0 world publication** separates root update and cell sync (race by
  inspection).
- **v0 host-namespace eval** leaks redefinitions across forks (X1, measured).

## 12. Plan

The first demonstration is **wandler with staging applied systematically**
(`04-demo-plan.md`), built from a Clojure REPL on existing libraries (wandler,
ansatz, spindel, v0), with Klara as a library. RFCs (`rfc/`) are cut from this
document and updated as experiments land.
