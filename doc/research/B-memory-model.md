# B — Memory model (research note, iteration 0, 2026-10-27)

Status markers as in `doc/signature.md:10-13`: **Holds** (argued or measured,
with evidence), **Conj** (plausible, unproven), **Open** (unknown, or the
statement is not yet right). Paths are relative to `Development/`.

## 0. Disagreements first

The working thesis was: values carry a copy comonoid and resources don't;
forking means copying, so only values fork; regions are affine inside and
persistent across fork boundaries, with `freeze` at the boundary; uniqueness
comes from RC=1 or from a static proof. Six objections, ordered by how much
they change the design:

1. **"Only values fork" is false in our own code.** spindel forks its own
   mutable atoms by per-entity copy-on-write (`spindel/docs/atoms.md:56-76`).
   It also forks external systems that implement yggdrasil branching, settled
   through an affine `ForkHandle` (`spindel/docs/forking.md:90-110`).
   `signature.md:90-95` already separates `σ` (weight-preserving split on `W`)
   from `Δ`. So there are **three fork structures, not one**: `Δ` for values
   (free), `σ` for evidence and RNG keys (linear split), and `branch!` for
   branchable resources (an effect that returns a fresh identity, with
   settlement exactly once). The rule should read "forkable = has a fork
   structure; copyable is the free special case."
2. **`freeze` is not a semantic operation.** If the meaning of a program is
   its value semantics, then freeze and thaw are the identity on meanings.
   They are realization operations, like Perceus's `dup`/`drop`. On an RC
   host freeze is a no-op: a fork bumps the count and the next write copies.
   Freeze is needed only on hosts without RC. Keep it out of the core
   calculus. Otherwise the narrowing principle ("annotations never change
   meaning", `00-design-space.md` §Decided) has a hole the size of a primitive.
3. **The Lean study's verdict "JVM dynamic layer irrecoverable" is too strong**
   (`lambda-join/studies/lean4-runtime.md:124-130`). Clojure's transients
   already carry a sound runtime uniqueness check, the per-node `edit`
   owner token, with O(1) thaw and freeze ([clojure.org/reference/transients](https://clojure.org/reference/transients)).
   It checks a weaker property than RC=1: "allocated or copied in this
   region since it opened". A missed check degrades to a copy, never to
   unsoundness, *provided the token never escapes the region*. Proving that
   one fact is much cheaper than proving each value unique.
4. **But on token hosts every fork pays more than on RC hosts. I measured
   this (§6).** With tokens, a fork must revoke ownership for *all*
   children, including the one child that is in fact unique. My attempt to
   hand the token to the first child was unsound: the duplicate's copied
   spine still shared leaves owned by that token. RC avoids this because
   counts live per node. Expected cost: once every node gets touched, about
   1/(duplicate fraction) more copying. That is roughly 2.7× under
   multinomial resampling.
5. **`K` (continuations) is listed as copyable** (`signature.md:27`). A
   continuation or closure that captures an `R` or a `W` is not copyable.
   Copyability must be *derived* from what a closure captures. metacarp takes
   the opposite default and makes every function value affine
   (`metacarp/carp-ownership/carp-ownership.carp:201-205`). Smaller
   inconsistency: `doc/algebras.md:517` calls `branch` "duplication of the
   future", while `signature.md:87-97` assigns the future to `split`.
6. **Representation matters as much as uniqueness.** In the §6 measurements,
   persistent → region-transient gave 2.3–4.3×. Transient → flat unboxed
   leaves with tokens gave another 1.7–3.2×. That makes "relayout never
   changes meaning" a first-class obligation, and it fails today in one
   concrete place: hash-map iteration order is observable, and it differs
   between HAMT and CHAMP.

## 1. What prior docs and repos already settled

- **CD-category objects** (`lambda-join/doc/signature.md:19-31`): `V`, `P`,
  `K`, `H` and `T` support copy and discard. `W` supports neither (linear).
  `R` supports discard only (affine). "Weights and evidence may be split,
  never copied" (`:45-47`). There is no concurrency primitive, because "`R`
  not admitting `Δ` is the whole content" (`:287-288`). L10, the claim that
  no derivation admits `Δ_W`, is still **Open** (`:265`).
- **Memory ladder, D21** (`doc/design-decisions.md:907-925`;
  `doc/language.md:230-247`): (i) persistent by default; (ii) automatic reuse,
  with full Perceus on owned runtimes and "proved-linearity transients" on
  JVM/JS; (iii) escape-analysis mutation kept limited in reach; (iv) borrow
  islands, described as "Carp minus lifetimes plus pins", with no suspension
  points inside islands.
- **Lean 4 runtime** (`studies/lean4-runtime.md`): the exclusivity check is
  "one load, two compares" (`:33-35`). Reuse is a runtime branch, "never a
  semantic bet" (`:52-57`). The static layer travels to other hosts and the
  dynamic layer does not (`:114-139`). Crossing a thread is a one-way door
  (`:78-92`, `:187-188`). Persistent `rc=0` objects pay no RC (`:88-92`).
- **Koka** (`studies/koka.md:112-136`): drop specialization and field-diff
  reuse. Multi-shot resumptions are made safe by precise `dup`. fip/fbip is
  an opt-in, graded, per-function certificate, which is the trust-ledger
  shape.
- **Roc** (`studies/roc.md:126-151`): uniqueness is a runtime `rc==1` check,
  and borrow inference exists to keep counts at 1. Refcounts are
  thread-confined.
- **Valhalla** (`design-decisions.md:680-697`; `studies/valhalla.md:40-53`):
  trie spines never flatten. The gains are in leaf entry arrays,
  strict-final flat fields in node classes, and scalarized cursors.
  Non-atomic flat leaves need a release fence at publish.
- **Publication by `releaseFence`** (`design-decisions.md:709-712`): build
  with plain writes and fence once at publish. This is "freeze-then-fence".
- **World value** (`doc/state.md:12-31`): runtime state is one persistent
  value, so snapshot and fork are free. Merge is a π-checked join.
  Measured: 0.75× of `dosync` (`:110-118`).
- **Multi-shot continuations and persistence are one design**
  (`doc/algebras.md:529-541`): closures are multi-shot whenever their
  captured state is aliasable. A `branch` inside a host-capture region
  forces a deoptimization.
- **Checker-licensed transients reached 2.37× in Christian's Typed Clojure
  fork** (`design-decisions.md:484-489`).
- **Narrowing ladder** (`doc/narrowing.md:20-27`): the affine rung is
  Carpaccio/Meta-Carp, whose ownership contract is EDN.
- **metacarp**: a type is owned iff it has a `delete`. Copying is always
  explicit, "never an action inserted here"
  (`metacarp/carp-ownership/README.md:10-15,31-33`). Capturing an owned
  value is a move (`carp-ownership.carp:909-914`). Parameter effects are
  Copy, Take, SharedBorrow and UniqueBorrow (`metacarp/docs/semantic-delta.md:21-25`).
- **carpaccio**: arenas are regions, and closing one invalidates its views
  (`carpaccio/docs/ownership.md:120-135`). Freeze is an **O(n) copy**:
  `snapshot` "copies a shared value into an ordinary persistent Clojure map"
  (`carpaccio/src/carpaccio/shared.clj:354-355`). There is no thaw.
- **raster**: uniqueness is a static, let-local, syntactic check:
  `can-reuse? (and unique? (or last-use? consumed?) (not escapes?))`
  (`raster/src/raster/analysis/memory.clj:204-214`). On the JVM, raster
  relies on C2's escape analysis (`raster/src/raster/compiler/core/types.clj:82`).
  Its rule "seal under a new address" (`raster/design/durable-numerical-state.md:106-108`)
  is freeze at the disk tier.
- **spindel**: a fork is an O(1) copy-on-write overlay. It follows the
  parent on shared paths and is "deliberately not symmetric snapshots"
  (`spindel/docs/forking.md:3,35`). Executors and external I/O are shared or
  repeated, not forked (`:77-88`). Plain Clojure atoms are "NOT fork-safe"
  (`spindel/docs/atoms.md:26-29`).
- **yggdrasil**: snapshots are immutable and every copy-on-write system
  implements them (`yggdrasil/src/yggdrasil/protocols.cljc:59-60`).
  Overlays are `:frozen`, `:following` or `:gated`
  (`yggdrasil/DESIGN.md:136-139`). GC is registry refcounting that never
  deletes, plus mark-and-sweep with a grace period
  (`yggdrasil/src/yggdrasil/gc.cljc:2-19`).
- **datahike**: branches are root pointers that share index nodes
  (`datahike/doc/versioning.md:9,34`). GC is mark-and-sweep from branch
  heads, and "branch heads are always retained" (`datahike/doc/gc.md:28`).

## 2. External survey (verified)

- **Perceus** (Reinking, Xie, de Moura, Leijen, PLDI'21,
  [doi:10.1145/3453483.3454032](https://doi.org/10.1145/3453483.3454032)):
  precise RC from a linear resource calculus, proved garbage-free, with
  reuse when RC=1.
- **Frame-limited reuse** (Lorenzen–Leijen, ICFP'22,
  [doi:10.1145/3547634](https://doi.org/10.1145/3547634)) bounds how long
  reuse may retain memory.
- **FP²** (Lorenzen, Leijen, Swierstra, ICFP'23,
  [doi:10.1145/3607840](https://doi.org/10.1145/3607840)): a linear calculus
  of fully-in-place functions that need no allocation and constant stack.
  It is checked in Koka and executed in place through Perceus whenever the
  runtime finds uniqueness.
- **Counting Immutable Beans** (Ullrich–de Moura, IFL'19,
  [arXiv:1908.05647](https://arxiv.org/abs/1908.05647)): borrow inference
  and reset/reuse. This is the precursor to Perceus, not a follow-up.
- **Mutable value semantics** (Racordon, Shabalin, Zheng, Abrahams, Saeta,
  JOT 21(2) 2022,
  [doi:10.5381/jot.2022.21.2.a2](https://doi.org/10.5381/jot.2022.21.2.a2)):
  fixed-size values go on the stack, and growable containers use
  copy-on-write keyed on uniqueness. Swift's realization is
  `isKnownUniquelyReferenced` over *atomic* RC. Swift's non-copyable types
  ([SE-0390](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0390-noncopyable-structs-and-enums.md))
  are exactly "a resource has no copy comonoid".
- **Clean uniqueness typing** (Barendsen–Smetsers, MSCS 1996,
  [doi:10.1017/S0960129500070109](https://doi.org/10.1017/S0960129500070109)):
  static uniqueness as a type attribute.
- **Regions.** Tofte–Talpin (Inf. & Comp. 1997,
  [doi:10.1006/inco.1996.2613](https://doi.org/10.1006/inco.1996.2613)).
  Cyclone (Grossman et al., PLDI'02,
  [doi:10.1145/512529.512563](https://doi.org/10.1145/512529.512563)).
  **Verona** (Arvidsson et al., OOPSLA'23,
  [doi:10.1145/3622846](https://doi.org/10.1145/3622846)): a forest of
  isolated regions with one "window of mutability" per thread. "Permanently
  immutable structures are created by constructing a mutable region and then
  turning its entire contents immutable through an explicit freeze"
  ([arXiv:2309.02983](https://arxiv.org/abs/2309.02983) §2). This is the
  closest prior art to our `freeze`. Pony's `iso`→`val`
  ([doi:10.1145/2824815.2824816](https://doi.org/10.1145/2824815.2824816))
  is the same move, done with capabilities.
- **Persistent structures.** HAMT (Bagwell, "Ideal Hash Trees", EPFL 2001).
  CHAMP (Steindorfer–Vinju, OOPSLA'15,
  [doi:10.1145/2814270.2814312](https://doi.org/10.1145/2814270.2814312)):
  separates data and node arrays, which gives a different iteration order
  from a HAMT. RRB vectors (Stucki, Rompf, Ureche, Bagwell, ICFP'15,
  [doi:10.1145/2784731.2784739](https://doi.org/10.1145/2784731.2784739)).
- **JVM.** Escape analysis (Choi et al., OOPSLA'99,
  [doi:10.1145/320384.320386](https://doi.org/10.1145/320384.320386)).
  Graal partial escape analysis and scalar replacement (Stadler,
  Würthinger, Mössenböck, CGO'14,
  [doi:10.1145/2544137.2544157](https://doi.org/10.1145/2544137.2544157)).
  [JEP 401](https://openjdk.org/jeps/401) value objects, status Integrated
  (preview). The JVM has no RC and no header bits we control.
- **Concurrency.** Biased RC (Choi, Shull, Torrellas, PACT'18,
  [doi:10.1145/3243176.3243195](https://doi.org/10.1145/3243176.3243195)):
  non-atomic counts for the owning thread. LXR (Zhao, Blackburn, McKinley,
  PLDI'22,
  [doi:10.1145/3519939.3523440](https://doi.org/10.1145/3519939.3523440)):
  RC for young objects combined with tracing. Clojure 1.7 *removed*
  transients' thread-owner check (clojure.org, above).
- **PPL precedent, closest to Christian's field.** Probabilistic C (Paige–Wood,
  ICML'14, [PMLR 32](https://proceedings.mlr.press/v32/paige14.html)) forks
  SMC particles with POSIX `fork()`. That is copy-on-write at page
  granularity, and it forks a *resource*: the whole process. Birch's lazy
  object copy (Murray 2020,
  [arXiv:2001.05293](https://arxiv.org/abs/2001.05293)) is copy-on-write
  over a mutable object graph, built for population methods. Both confirm
  that fork plus in-place update is the workload SMC actually runs.

## 3. Options and trade-offs

| Option | In-place condition | Fork cost | What breaks |
|---|---|---|---|
| **A. Persistent only** (Clojure today) | never | O(1) | 4–25× slower update loops (§6) |
| **B. Static uniqueness only** (Clean, raster, metacarp) | proof | O(1); the proof must stop at fork | no safety net. Analysis gaps cost speed, and analysis bugs cost soundness. Futhark does not trust its own surface types (`design-decisions.md:154`) |
| **C. Runtime RC=1** (Perceus/Lean/Roc/Swift) | `rc==1` | `dup` = O(1); the unique child keeps reuse | needs an owned object model (owned hosts only). Cycles leak. Crossing threads costs atomics or a marking walk |
| **D. Region tokens** (Clojure transients, Verona) | `node.owner == token` | revoke the token; every child path-copies lazily | the token must not escape. The unique child loses reuse (§0.4) |
| **E. Eager deep copy at fork** (Birch-eager, process `fork()`) | always (mutable) | O(state) per duplicate | value semantics. Only safe behind an island boundary |

C and D are the same idea at different granularity: a dynamic check with a
copy fallback. **B is the static half that every host shares** (the Lean
verdict). The choice per host is therefore C+B or D+B, never B alone.

## 4. Recommendation for Klara v1

**4.1 Semantics (host-independent, goes in the spec).** Every object
belongs to exactly one sort, fixed by its structure:

| Sort | Structure | Examples |
|---|---|---|
| **Value** `V` | `Δ`, `!` free | scalars, keywords, symbols, strings, Klara/Clojure persistent collections, programs `P`, frozen snapshots, closures and thunks whose captures are all values |
| **Affine resource** `R` | `!` only (an explicit or scheduled drop) | channels, file handles, Java objects by default, linked-mode Clojure atoms, arrays |
| **Linear** `W` | `σ` only (split, mass-preserving) | weights and evidence. Proposed: RNG keys (Q1) |
| **Branchable** `B` | `!`, plus the effect `branch! : B → B ⊗ Settle` | yggdrasil systems, datahike connections, the world, spindel atoms |

- **Resource** means: some observation distinguishes `x` from a copy of `x`.
  Identity or external effect is part of its behavior.
- **copy** (`Δ`) means share. RC increment on owned hosts, nothing on GC
  hosts. Never a deep copy.
- **discard** on a value is RC decrement or nothing. On an `R` it is a
  drop, scheduled deterministically at region exit (RAII). It is never left
  to finalization.
- **freeze** and **thaw** do not exist in the semantics. Surface
  `transient`/`persistent!` mean the identity on values, plus an affine
  discipline on the transient handle.
- **Classifying host objects.**
  - Java objects are `R` unless they are on an allowlist: String, boxed
    numbers, BigInteger and BigDecimal, UUID, java.time, records and
    JEP 401 value classes whose fields are all values. A `^:value`
    assertion also makes one a value, and it carries blame in the ledger.
  - Clojure atoms in *linked* mode are `R`: shared and not forked, which
    matches `spindel/docs/atoms.md:28`.
  - In *hosted* mode, `atom` denotes a world cell (`state.md` layer 1) and
    is `B`, which is what spindel's atoms already do.
  - A promise splits into a linear writer and a copyable reader.
  - A `line-seq` is an `R`, because its thunk captures a reader.

**4.2 Uniqueness evidence (static and shared across hosts).** Each update
site gets a three-point grade: *proved-unique* ⊐ *runtime-checkable* ⊐
*unknown*.
- The producers are let-local escape analysis (raster's `memory.clj`
  shape), Lean-style borrow inference, and optional affine and FP²-style
  annotations as certificates.
- The grade selects a representation. It never selects a meaning.

**4.3 Fork rule.** A fork applies each sort's fork structure: `Δ` on
values, `σ` on `W`, `branch!` on `B`. A fork over a live `R` is a static
rejection, or a dynamic error at Tier H. A fork never occurs inside an
affine island: islands carry no `split`/`branch` effect, which extends
`language.md:241-244`. `W` *may* enter islands, since accumulating a weight
is linear and harmless.

**4.4 Per-host realization.**

| Host / tier | copy | Uniqueness check | In-place iff | freeze | fork | Thread crossing | Reclaim |
|---|---|---|---|---|---|---|---|
| Interpreter (sci-like seed) | share | none | never (rung i) | — | share | safe (immutable) | host GC |
| **JVM, linked** | share | none (Clojure colls are adopted) | explicit transients only | `persistent!` O(1) | share | `releaseFence` on publish | tracing GC |
| **JVM, hosted** | share | region token per node (Klara CHAMP/RRB with primitive and flat leaves) | `owner==tok` ∧ token non-escaping (static) | revoke token + `releaseFence`, O(1) | freeze, then share; children path-copy lazily | tokens thread-confined, check kept (one compare) | tracing GC; C2/Graal scalar-replace non-escaping temporaries |
| JS | share | region token | as JVM | revoke | as JVM | n/a (workers copy) | tracing GC |
| WasmGC | share | region token | as JVM | as JVM | as JVM | — | host GC |
| **Wasm linear / native (owned)** | `dup` | `rc==1` (Lean header) | `rc==1`, plus FBIP/fip certificates | no-op | `dup`; the unique child keeps reuse | Lean `mark_mt` (one-way, O(subgraph)); evaluate biased RC | precise RC; resources in fiber-scoped arenas |
| **Disk** (konserve/datahike) | root pointer | never (content-addressed means immutable) | only in-memory dirty nodes before flush | flush + hash ("seal under new address") | `branch!` = new root pointer, O(1) | n/a | mark-and-sweep from branch heads, with grace period |
| **Remote** (replikativ/yggdrasil) | ref by hash | never | never | replicate | `branch!`; merge = π-checked join | n/a | per-system GC via yggdrasil |

**4.5 Storage tiers: one rule.** *Mutability lives only in the innermost
tier where uniqueness is known, and moving outward is freeze at that
tier's granularity.*
- register → heap is materialization: scalar replacement undone at an
  escape.
- heap → disk is token revocation, then hash and flush.
- disk → remote is replication.
- Moving inward is thaw: lazy path copying.
- Fork costs O(1) on every tier, because every tier shares structure.
- Reclamation is the one thing that differs per tier: RC, tracing, or
  mark-and-sweep from roots.
- Identity is a pointer in the heap and a hash on disk. Value equality must
  agree with both (obligation O4).

**4.6 Representation freedom.** Relayout preserves meaning iff:
- (a) value identity is unobservable. `identical?` is a may-alias hint, and
  values cannot be locked on or put in identity maps;
- (b) `=` and hashing are structural and independent of layout, which
  extends `hasheq` parity to flat and primitive leaves;
- (c) iteration order of unordered collections is *unspecified*, and the
  corpus randomizes it;
- (d) floating-point relayouts (SIMD reassociation) carry an ε grade under
  principle 5, not ε=0;
- (e) no transient is reachable from a frozen value.

**4.7 Cycles, laziness, closures.**
- Values are acyclic by construction: immutable and built strictly.
  Recursion goes through world names (vars resolve via the world value) and
  through code pointers after lambda lifting, never through env cells.
- Lazy self-reference (`(def fibs (lazy-cat … fibs …))`) creates a cycle
  through a memo cell. On owned hosts it leaks.
- Cycles among resources are scoped by arenas owned by a fiber or world.
- v1 ships no backup cycle collector, following Lean and Koka. The leak is
  documented and the corpus probes it.
- A closure or thunk is a value iff all its captures are values. This is a
  bit computed at creation, like Rust's auto traits.

**4.8 The metacarp seam.**
- Klara values enter islands as `SharedBorrow`, or as `Copy` if blittable.
  A `Take` (move) needs a uniqueness grade of at least runtime-checkable.
- Island outputs leave through an O(1) freeze into Klara collections.
  This replaces carpaccio's O(n) `snapshot`.
- **What forkability costs affine code:**
  - no fork points or multi-shot capture inside islands;
  - every heap value needs a uniqueness word: an 8-byte RC header owned,
    or one owner reference per node on the JVM;
  - no identity-observable operations on values.
- **What affine code costs forkability:** a fork can only happen at an
  island boundary. In SMC that is natural: one island per particle step,
  with resampling between islands.

## 5. Obligations and falsifiers

| # | Claim | Status | Falsifier / evidence |
|---|---|---|---|
| O1 | Heap freeze is O(1) on every host | **Holds** | Clojure `persistent!` (clojure.org); a no-op under RC. carpaccio's `snapshot` violates it today |
| O2 | The token scheme is sound: no write is observable through a frozen value | **Conj** | a program where the token escapes (closure capture, async handoff) and a frozen value changes. Proof target: tokens are reachable only from region-local roots |
| O3 | On token hosts the unique child cannot keep reuse without per-node counts | **Holds** (argued and observed §0.4) | a sound transfer scheme that needs no node-level metadata |
| O4 | Relayout invariance (4.6 a–e) | **Conj** | a corpus program whose output changes between HAMT and CHAMP. It exists as soon as anything prints `(seq m)`. Hence (c) |
| O5 | Values are acyclic | **Conj** | lazy self-reference leaking on Wasm |
| O6 | Closure copyability derived from captures is sound and cheap | **Conj** | a captured `R` reachable from a forked closure; more than 2% call overhead |
| O7 | Annotations never change meaning (gradual guarantee) | **Holds** if freeze/thaw are identity *and* every proved site keeps its runtime check. **Conj** where a check is elided on proof alone | a differential test that strips annotations and compares outputs |
| O8 | No derivation admits `Δ_W` (L10) | **Open** | `signature.md:265` |
| O9 | Thread crossing (`mark_mt` walk) is affordable for particle-parallel SMC | **Open** | walk time above 10% of step time at N=10⁴ |
| O10 | JVM hosted (tokens + flat leaves) stays within 3× of mutable clone-on-dup | **Open**, partly confirmed | §6: ahead at K≤16, 2.6–3.4× behind at K≥256 |
| O11 | The owned tier is the performance reference for fork-heavy code | **Conj** | Perceus fails to beat JVM tokens by ≥2× at K=16 (E2) |

## 6. Smallest experiment

**E1 (run, indicative).** SMC skeleton: N=1000 particles, each state a
1024-element vector. Per step, K random writes, then multinomial resampling
(fork). T=30 steps. GraalVM JDK 25, stock Clojure CLI, median of 5 after 3
warm-ups, one machine. Scripts:
`/tmp/claude-1000/-home-christian-weilbach-Development-clojure/d015cfe9-5606-4419-ab30-07ea212bf22a/scratchpad/bench/bench.clj`
and `bench2.clj` in the same directory.

| K | persistent `assoc` | transient region (freeze at fork) | flat long[32] leaves + token | mutable `long[]` + clone-on-dup |
|---|---|---|---|---|
| 1 | 39 ms | 78 | 11–17 | 38 |
| 16 | 226 | 98 | 55–59 | 41 |
| 256 | 1445 | 405 | 196–225 | 65 |
| 1024 | 6025 | 1391 | 439–552 | 169 |

How to read it:
- Region transients beat persistent by up to 4.3×.
- Flat unboxed leaves beat transients by a further 1.7–3.2×. This is the
  representation gain from §0.6.
- The remaining gap to clone-on-dup at saturation is the cost of losing the
  unique child (§0.4): tokens copy every child, while counting copies only
  duplicates.
- At K=1, the transient costs *more* than persistent, because thawing
  allocates a fresh tail and root. A single-write region should not be
  thawed at all, and the uniqueness grade must account for that.

**E2 (next, about 2 days).**
- Port the same workload to Koka (Perceus) and Lean 4 (`Array` with
  reset/reuse), plus a JMH version of the JVM variants.
- Vary the duplicate fraction (multinomial vs systematic resampling) and
  the state size M ∈ {64, 1024, 65536}.
- Report time, bytes allocated, and copies per step.
- O11 is decided by Perceus vs JVM tokens at K=16. O10 is decided by tokens
  vs clone-on-dup at K≥256.
- Add a deliberate token-escape test, a transient captured in a closure
  that runs after the fork, to drive O2's dynamic guard.

## 7. Questions for Christian

1. **Should RNG keys be linear, like `W`?** JAX-style splittable keys reuse
   `σ`, so using the same key twice becomes a type or runtime error, and
   correlated particles are a classic SMC bug. The cost is REPL ergonomics:
   you can no longer just call `(rand)`. Option: a linear key inside
   inference handlers and ambient randomness outside them.
2. **What does `branch` mean: a frozen snapshot or a parent-following
   overlay?** Value semantics says snapshot: the branch never sees later
   parent writes. spindel's default follows the parent on shared paths for
   efficiency (`forking.md:35`). Following is cheaper for speculative
   rebase, but it is not `duplicate` in the comonad sense, so L2/L5 would
   need restating. My recommendation: snapshot as the meaning, and
   following as a separately named operation.
3. **Should hash-map iteration order be unspecified?** If it is, we can
   swap HAMT, CHAMP or flat layouts freely, and the corpus shuffles order
   to catch code that depends on it. If not, we are locked to Clojure's
   HAMT order for the life of the language. Some real Clojure code
   accidentally depends on map order, so this is a compatibility-vs-speed
   decision.
4. **Should `identical?` exist for Klara values?** If it can be observed,
   the compiler may not merge or split representations. Proposal: keep it
   as a "may-alias" hint that is allowed to answer false negatives.
5. **In hosted mode, should `atom` mean a forkable world cell rather than a
   JVM cell?** Code would behave differently under `require` (linked) and
   under Klara's expander (hosted). That is honest, since forking a real
   shared cell is impossible, but it is a visible semantic split.
6. **Cycles on the owned runtime: document the leak, as Lean and Koka do,
   or build a backup collector for resources and lazy memo cells?** The
   collector costs months of work. The leak costs a footgun for
   self-referential lazy sequences.
