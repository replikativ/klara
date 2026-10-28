# RFC 0005: Affine regions, and moving checks across binding times

- Status: draft (semantics first; implementation plan in §7)
- Owner(s): Christian Weilbach; open questions on native lowering with Veit Heller
- Builds on: RFC 0001 (authority, S6), RFC 0002 (effects), research notes B (memory model), J (type systems as predictors), N (metacarp unification)
- Obligations: AF1–AF8 below

## Motivation

Christian wants to write affine programs optionally in Klara, in the spirit
of Carp: owned values updated in place, deterministic release, static
accounting at the top level if desired — while fitting the forking memory
model cleanly, and compiling to several emitters (JVM bytecode, JS, native via
metacarp or C). The design must not be a second mechanism next to the existing
one: Klara already enforces affinity *dynamically* for authorities (S6). This
RFC extends that mechanism, gives it an algebraic reading, and shows how
staging turns the dynamic discipline into a static one and back.

## 1. The current codebase, as one picture

```
 source ──reader (:klara feature)──▶ forms
   │ klara.expand  (scope sets, recorded world reads, syntax extensions in the world)
   ▼
 core terms (klara.core: 12 forms + code/esc)          spec/ (ansatz): small-step rules,
   │                                                    proofs; spec-diff test ↔ T0
   ▼
 klara.eval — T0 CEK machine  [mode control env kont]
   │   env  = {:locals :basis root :mint}
   │   kont = list of data frames (handle, branch, fork-scope, shot, wrap, …)
   │   effects: lexical instances (user ops) / dynamic handlers (ambient ops)
   │
   ├──▶ klara.world      immutable roots, CAS publication, forks, fibers, bases
   ├──▶ klara.authority  STORE Σ : Id ⇀ State (kind, status, scope ctx, payload, gen)
   │                     split rules per kind; settlement; intents; receipts
   ├──▶ klara.code       code values, levels, scope-extrusion liveness, lift, genlet
   └──▶ klara.stage      executables keyed by (CodeId, assumptions); guards; certificates
                         (S7: per-root validity, frame-state deopt; S8: compile tier)
```

The affine design adds exactly one authority kind to `klara.authority`, a
small family of ambient operations handled like `:auth/*`, a static checker
(`klara.affine`) that produces derivations, and an erasure step in the
compile tier. Nothing else changes shape.

## 2. Algebra: authorities are resource algebras

Read RFC 0001's authority kinds as **resource algebras** in the sense of
separation logic (partial commutative monoids of "shares", cf. Iris resource
algebras, Jung et al.): a fork *splits* an element, settlement *recombines*,
and an operation is allowed only when the share it needs is held.

| Kind | Carrier of shares | Composition `a · b` | Splittable? |
|---|---|---|---|
| resource | Excl(r) | undefined (exclusive) | no — transfer only |
| evidence | mass ℚ≥0 | + | yes (mass-preserving) |
| budget | vectors ℚ≥0^C, hard components | + | yes (hard components bounded) |
| randomness | keys, split : k ↦ (k₁, k₂) | (only via split) | yes |
| branchable | sets of systems | disjoint union | yes (partition) |
| **owned** (new) | **Excl(write) + Frac(read)**: the full share 1 permits writes; a fraction q ∈ (0,1] permits reads | fractions add up to ≤ 1 | **reads yes, writes no** |

The owned row is the classical *fractional permission* model (Boyland, SAS
2003): a borrow takes a fraction for a scope and returns it; a write needs
the whole. It gives Klara affine values without inventing a new discipline.

**Owned operations** (ambient effects `:own/*`, handled by the authority
reference handler, specified as transitions on Σ):

```
alloc v             ∅            ⇝  own(ℓ, v, 1)                 returns ℓ
read ℓ              own(ℓ, v, q>0) ⇝ own(ℓ, v, q)                returns v
update ℓ f          own(ℓ, v, 1) ⇝  own(ℓ, f v, 1)               write needs the whole share
borrow ℓ q (body)   own(ℓ, v, 1) ⇝  own(ℓ, v, 1−q) ⊗ lent(ℓ, q)  scoped; returned at scope exit
move ℓ              transfers own(ℓ, …) to the callee's context
freeze ℓ            own(ℓ, v, 1) ⇝  settled                       returns v (a copyable value)
drop ℓ              own(ℓ, v, 1) ⇝  settled                       deterministic release
```

**Value semantics is preserved**: `update` *means* replacing the cell's value
by `f v`; the old value is unreachable because nobody else holds a share.
Updating in place is a representation choice licensed by that fact — not part
of the meaning. Erasing every affine annotation yields a program that copies
instead of mutating, with the same observations (narrowing doctrine).

## 3. Forks and affine regions

Fork already splits every authority a computation holds (RFC 0001, S6). The
owned row's split rule settles the interaction with no new theory:

- a **full share** (write permission) cannot be split → a fork inside a
  region that holds a live owned value for writing is **rejected**, by the
  existing rule;
- a **read fraction** can be split → read-only borrows may cross a fork, each
  branch reading with q/2;
- **freeze** turns an owned value into a copyable value: the bridge from the
  linear world to the persistent one.

Hence the shape of affine programs:

```
persistent world ──fork──▶ … ──▶ [ affine island: alloc / update in place / borrow ] ──freeze──▶ value ──fork──▶ …
                                   inputs: borrowed (fraction) or moved (full share)
```

Forks happen between islands; inside, effects are restricted to
tail-resumptive and abortive operations (no continuation captured through
owned frames — the same rule note N derives for native frames). A whole
program may be one island (Carp-style top level); it then forks only at its
edges (per request, per simulation step).

Categorically: the copyable values form the data monoidal computer; owned
cells live in the linear world it acts on (note A's two-world structure);
`freeze` is the map from linear to copyable (Benton's linear/non-linear
adjunction is the standard reading).

## 3a. Persistent data structures, transients and the storage tier

Klara's persistent collections — Clojure's, the clean-room CHAMP/RRB ones,
and replikativ's `persistent-sorted-set` (PSS) with the databases built on it
(datahike's indices) — fit the owned row directly:

```
persistent value v ──transient──▶ own(ℓ, v, 1)  (path copying on first write, structural sharing with v)
                     update!/conj!/disj!  in place on nodes created inside the region
own(ℓ, v′, 1) ──persistent!──▶ v′           (= freeze, O(1))
v′ ──flush/seal (konserve, IStorage)──▶ content-addressed nodes (= freeze at the storage tier)
```

- **`transient` = alloc of an owned cell whose value shares structure with a
  persistent value; `persistent!` = freeze.** The old value stays valid: only
  nodes created inside the region are mutated (path copying), so other
  holders of `v` are unaffected — value semantics holds.
- **Edit tokens are runtime uniqueness evidence** (grade D/A): Clojure's
  transients and PSS (`Settings._edit`, an `AtomicReference<Thread>`) mark
  nodes owned by the current editor. In Klara the editor must be the **owned
  authority (region/fiber context), not the host thread**: two forks or two
  fibers can run on one thread, and a fiber can move between threads, so a
  thread-identity token is unsound under the fork model. The static checker
  (S grade) erases the token check entirely.
- **Database transactions are affine islands**: a datahike transaction builds
  its index updates through PSS transients, then freezes them into the new db
  value; forking a db is sharing persistent roots. The island/fork rule of §3
  is exactly the transaction boundary.
- **The storage tier is one more freeze**: flushing dirty nodes to konserve
  (PSS's lazy durable storage, its content-addressed mode for CRDT sync)
  seals them under content addresses (research note B §4.5: mutability lives
  only in the innermost tier where uniqueness is known; moving outward is a
  freeze at that tier's granularity). The address scheme should follow
  RFC 0004 (canonical EDN, building on hasch).

Implementation consequence: the transient protocol of every persistent
collection Klara uses (Clojure's via its interfaces, CHAMP/RRB, PSS) is
wrapped so that its edit token is bound to the owned authority. For PSS this
is a change in PSS itself (an editor object instead of a thread), which
benefits datahike independently of Klara.

## 4. Moving checks across binding times

Every authority operation has a **check**: the precondition on Σ (does the
caller hold the needed share?). The check is ordinary code in the reference
handler. Staging decides *when* it runs:

| Grade | Check | Realization |
|---|---|---|
| D (dynamic) | at every use | the authority store (S6 today) |
| A (stable) | once per region entry, cached | a guard: "ℓ uniquely owned under this root" |
| S (static) | before running | a derivation from the affine checker; the check is erased |

**Dynamic → static.** Specializing a region with respect to ownership facts
(a checker derivation, an escape-analysis fact, or a guard) partially
evaluates the handler's checks: when the facts entail the precondition, the
check disappears from the residual program.

**Static → dynamic.** When statically checked affine code is called from
dynamic code, the facts it assumes but cannot verify (the argument really is
uniquely owned; a borrow is not retained) become **boundary contracts** —
checks re-inserted at a later binding time (stateful contracts for affine
types, Tov & Pucella; to verify before citing in a paper).

**Check erasure (the theorem schema).** If the checker derives `⊢ r : affine`,
then the reference handler never fails on any run of `r`, so the program with
checks erased has the same observations: `⟦erase(r)⟧ = ⟦r⟧`. This is the
general pattern for every narrowing layer (effects, shapes, authorities):
a static derivation licenses removing the dynamic check it subsumes.

## 5. Two modes, one analysis

| Mode | Source of facts | On failure |
|---|---|---|
| inferred | escape/uniqueness analysis on ordinary code (S8's `klara.compile.escape`, raster's memory analysis) | stays persistent (optimization only) |
| declared | the programmer marks a region or definition affine | rejected with diagnostics (a checked claim) |

Both produce the same derivations; the declared mode turns them into
obligations.

## 6. Emitters

The same K2 regions, annotated with ownership facts, lower to:

| Emitter | Owned values become | Release |
|---|---|---|
| JVM bytecode | mutable arrays/objects, buffers reused in the region (raster's buffer fusion/hoisting is the existing instance) | GC; no allocation in hot loops |
| JS | typed arrays, in-place updates | GC |
| native C / Wasm linear | heap cells | deterministic free at last use (Carp/Perceus style) |
| metacarp (optional) | Carp values; Carp's checker re-verifies | Carp's plan |

metacarp is one emitter among these (as carpaccio uses it today), not the
definition of affinity.

## 7. Implementation plan (grounded in the current code)

1. **`klara.authority`**: add kind `:owned` with payload `{:cell v :share 1 :lent {}}`;
   its split rule (full share: none; read fractions: split); ops alloc, read,
   update, borrow, move, freeze, drop as transitions with the existing
   lifecycle, contexts and generation counters. Fork rejection comes from the
   existing split machinery.
2. **`klara.eval` / `klara.core`**: ambient namespace `own`, handled by the
   authority reference handler like `auth`; a restriction check that only
   tail/abort operations are performed while a full share is held.
3. **Surface** (`klara.expand`): `(own v)`, `(read o)`, `(update! o f)`,
   `(borrow [x o] body)`, `(move o)`, `(freeze o)`, `(drop! o)`, and a
   `(defaffine name [params] body)` / `^:affine` marker for declared regions.
   (Names to settle; the naming rule applies.)
4. **`klara.affine`**: a static checker over core terms for a first fragment
   (places = locals and owned cells; loans scoped by `borrow`; no aliasing of
   full shares), producing derivations attached to terms.
5. **Erasure** in the compile tier (S8's pipeline): a pass that removes `:own/*`
   checks covered by a derivation, then a representation pass that makes
   `update` in place.
6. **Spec**: extend the ansatz spec with a store Σ and the owned transitions;
   state and (later) prove check erasure for the fragment.
7. **Tests**: differential traces (checked vs erased) on accepted programs;
   rejection of forks holding a full share; read-borrow across forks;
   boundary contracts; a JVM emitter test showing no allocation in an affine
   loop.

## 8. Obligations

| Id | Obligation | Status |
|---|---|---|
| AF1 | Owned transitions preserve value semantics (erase annotations ⇒ same observations) | Open |
| AF2 | The checker is sound: `⊢ r : affine` ⇒ the handler never fails on `r` | Open |
| AF3 | Check erasure: `⟦erase(r)⟧ = ⟦r⟧` for checked regions | Open (follows from AF2) |
| AF4 | Forks reject full shares and split read fractions; mass of fractions conserved | Open |
| AF5 | Boundary contracts catch every violated assumption at the dynamic/static boundary | Open |
| AF6 | No continuation is captured through a frame holding a full share | Open |
| AF7 | In-place representation on each emitter is observationally equal to the functional update | Open |
| AF8 | Inferred and declared modes agree on accepted regions | Open |
| AF9 | Transients of every persistent collection are owned regions: edit tokens bound to the owned authority, never to a host thread; `persistent!` is freeze | Open (PSS uses a thread token today) |

## 9. Open questions

1. Surface names and syntax (carpaccio's `defcarp`/`defnative` style vs
   annotations on ordinary definitions).
2. General effects inside islands: is there a use case (inference?) that
   needs more than tail/abort operations while a full share is held?
3. Top-level strictness: fully checked islands, or affine by default with
   explicit escapes to persistent values?
4. Borrow lifetimes: lexical scopes only (simple, first) or named lifetimes
   (Carp/Rust style, later)?
5. Native lowering: which subset of the checker's derivations can be handed
   to metacarp so Carp's checker re-verifies rather than trusts (note N)?

## 10. Decisions (Christian, 2026-10-28)

- **Surface**: carpaccio style (`defaffine`-like forms) and metadata hints on
  symbols (`^:own`, `^:borrow`, `^:move`).
- **No reliance on metacarp for affinity.** Klara has its own checker, with
  its rules written in Klara's docs and spec and its derivations as
  inspectable EDN data. The JVM (via Clojure) is the first and reference
  emitter; metacarp remains an optional native emitter later. Reason: metacarp
  is an external native dependency requiring a C compiler, and Klara's
  semantics must be transparent and self-contained.
- **Borrow lifetimes**: lexical first; named lifetimes later (when views or
  slices into owned buffers need to be returned from functions).
- **Effects inside islands (Q2)**: only tail-resumptive and abortive
  operations for now; one-shot general effects (`await` for I/O into owned
  buffers) later; multi-shot only with an explicit copy per resumption, if ever.
- **Tracking (Q3)**: opt-in per value — only values created as owned are
  tracked; a strict opt-out (Carp/Rust) mode may come later per module.

## 11. Direction: language-level accounting (concept, not v1)

Christian wants general accounting on the language level, as `kontor` does
for dvergr. The resource-algebra reading of §2 already points there:

- **Every authority kind is an account type**: a commutative monoid of
  quantities plus a conservation law. Evidence (mass) and budget (vectors)
  already are; owned shares (fractions) are too.
- **Operations are postings**: fork splits a balance into child accounts,
  settlement closes them, spending debits; the double-entry invariant
  (debits = credits) is exactly the conservation obligations AU6 and budget
  conservation. The authority store's receipts are the journal.
- **Parametric (quantitative) ownership**: ownership types indexed by an
  amount — `own[q]`, a budget `{:cpu 3 :eur 0.5}`, an evidence mass — are
  graded/quantitative types (QTT, Granule; research note E). Leasing has a
  price: a borrow can post a fee to a budget account for its duration.
  (Veit's ownership annotations in metacarp are reportedly parametric in a
  similar way — to look at when this is designed.)
- **One ledger semantics** for the language (authorities) and for the
  product (kontor/dvergr accounts) would let agents' spending, inference
  evidence and memory ownership be audited with the same tools.

This deserves its own RFC once affine regions exist; it is recorded here so
the owned kind is designed as one account type among others, not a special
case.
