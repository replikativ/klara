# Klara architecture synthesis: diagrams, algebra, semantics (2026-10-27)

Consolidates `05-architecture.md` with research notes I (Chez, pattern) and J
(type systems as predictors). Three views of the same system: the pipeline
(what runs), the algebra (what the objects and maps are), and the semantics
(which squares must commute).

## 1. The pipeline view

```
                    ┌──────────── planning (meta level, budgeted) ───────────┐
                    │  predictor ladder: 0a types (cheap, always on)          │
                    │  0b refinement/proof (VOC-scheduled) · 1 cost models    │
                    │  2 learned surrogates · 3 profiles · 4 real runs        │
                    └──────┬───────────────────────────────▲─────────────────┘
                           │ decisions (what to specialize)│ receipts, evidence
                           ▼                               │
 source ──expand──▶ Core K0 ──analyze──▶ K1 effect-lowered ──specialize──▶ K2 ──emit──▶ K3
   (world reads      (12 forms,          (op classes:        (guards,          (JVM bytecode
    recorded)         CodeIds)            tail/abort/general) shapes, layouts,  │ Chez Scheme
                                                              certificates)     │ C/LLVM via
                                                                                │ metacarp
                                                                                ▼
                     ┌──────────── host: KRI ─────────────────────────────────────┐
                     │ values · memory · control · world cells · code load/guard  │
                     │ fibers · FFI · counters                                    │
                     └────────────────────────────────────────────────────────────┘
```

Ownership rule (note I): **Klara owns everything that reads the world** —
expansion, analysis, specialization, guards, invalidation, the predictor
ladder. A host back end (JVM emitter, Chez, metacarp) only turns closed K3
code into machine code. Chez is the native baseline; metacarp/LLVM is the
kernel route (T3).

Tiers per host:

| | JVM | native (Chez) |
|---|---|---|
| T0 | sci-style interpreter | Petite-style interpreter for huge/trivial forms |
| T1 | generic bytecode, var indirection | Chez-compiled generic code, var indirection, no inlining across cells |
| T2 | specialized bytecode with guards | Chez-compiled specialized code with guards (Klara supplies speculation; Chez has none) |
| T3 | raster kernels | metacarp/carpaccio kernels |
| continuations | selective CPS (measured 2.7× tax on transformed code) | segmented stacks (no tax on non-capturing code; needs no mutable-local lowering and an authority scan before a second resume) |

## 2. The algebraic view: objects and maps

```
          Data  ─────────── acts on ───────────▶  Authority world
   (monoidal computer:                         (linear: tokens for consume,
    values, programs P,                          branch, settle, evidence,
    copy/discard on all,                         budget, randomness;
    run : P⊗A→B,                                 split rules per kind;
    specialize : P⊗A→P)                          no copy)
```

- **Terms and programs**: Core terms modulo α; programs P are closed code
  values with CodeIds.
- **Handlers** are algebras for effect signatures; a reference handler fixes
  each effect's meaning; λ∨'s laws are equations the reference handlers
  satisfy; inference engines are other models.
- **Algebras as values** (stdlib): monoid, join (commutative monoid classified
  by divisibility), distance, measure, deltas — passed explicitly; their laws
  license rewrites at a stated level (proved / tested / documented).
- **Translations** T : model₁ → model₂ (compile, marshal, offload,
  coarse-grain) are **lax**: they preserve meaning up to a laxator ε and are
  *not* functorial in cost (fusion is the counterexample, note E).
- **Predictors** are **abstract interpretations**: a Galois connection
  α : concrete ⇄ abstract : γ per analysis (shapes, effects/op classes,
  captures/authority, refinements, grades); several combine as a reduced
  product over one AST, attached to the analyzer's evidence slots (note J).
- **Specialization** is s-m-n on P: `run(specialize(p,a), b) = run(p,(a,b))`.

## 3. The semantic view: squares that must commute

Each correctness claim in Klara is one commuting square (exact or up to ε).

**Adequacy (A1).** Operational and denotational semantics agree on observations.
```
   e ──── ⟶* (small-step, reference handlers) ────▶ observations
   │                                                     ▲
   ⟦·⟧                                                   │ obs
   ▼                                                     │
 weighted execution tree ────────── limit/normalize ─────┘
```

**Pass correctness.** Every compiler pass Kᵢ → Kᵢ₊₁ is a simulation.
```
   Kᵢ term ──── pass ────▶ Kᵢ₊₁ term
     │                        │
   ⟦·⟧ᵢ                     ⟦·⟧ᵢ₊₁
     ▼                        ▼
   meaning ─────── = ──────▶ meaning        (certified, tested, or trusted —
                                              recorded in the receipt)
```

**Specialization (s-m-n, A2(ii)).** Residuals are correct by construction once
the specializer is; proved passes stay proved when specialized.
```
   (p, a, b) ── specialize(p,a), then run on b ──▶ result
       │                                              ║
       └──────────── run p on (a,b) ─────────────────▶ result
```

**Guarded specialization.** Under the assumption set A (world cells, argument
guards), the residual agrees with the generic program; when A fails, control
returns to the generic path at region entry (replay) without repeating
effects.
```
   x ── guard_A(x)? ──yes──▶ residual(x) ─┐
        │                                  ├──▶ same observation
        └──no──▶ generic(x) ───────────────┘
```

**Predictor soundness.** An abstract fact over-approximates every concrete run
(γ ∘ α ⊒ id); a fact licenses a rewrite only if its level is 0a/0b
(certified) — levels 1–3 steer and never license.

**Translation (approximate).** `d(⟦T e⟧, ⟦e⟧) ≤ ε(T)` under the declared
metric; ε composes along pipelines by the error algebra (Lipschitz
composition), cost is measured.

**Snapshot fork.** Forking commutes with the world: a branch observes the
pinned parent root; authorities split exactly once (RFC 0001).

## 4. What note J changes

- Level 0 splits into **0a** (cheap, always on: shapes, op classes, captures)
  and **0b** (refinement/SMT, ansatz proofs: sound but expensive, scheduled by
  value of computation).
- **Sound facts that read other definitions** need no runtime guard but are
  invalidated on publication; facts about Tier H host code are always guarded
  or recorded as trusted. The assumption-set grades of note C cover all three.
- The prediction that pays most is **op-class absence plus latent effects**
  (Koka decides CPS this way): it decides where CPS regions and guards go.
- ansatz laws over `Nat` need an **overflow side condition** before they can
  license rewrites on JVM longs.
- **v1 predictor subset**: shapes with occurrence typing; effects with op
  classes and latent rows; captures with affine authority in place of data
  usage.

## 5. Open questions (from notes I and J)

1. Chez as native host (hybrid) vs blueprint — recommendation: host first.
2. Native memory: Chez's tracing GC gives up reference-counting reuse —
   acceptable for the first native tier, revisit after X5.
3. Op classes stay semantic on every host (recommendation) or become a hint
   where segmented stacks exist.
4. pattern needs matcher code generation before it can carry hot passes
   (25–33× slower than hand-written passes today) — upstream in
   replikativ/pattern.
5. Update ../ChezScheme to v10 (the checkout is from 2020).
6. Relicensing the Typed Clojure fork's own files (if solely Christian's).
7. Held-out discipline (G9) is covered by no type system; it stays a runtime
   evidence rule.

## 6. Decisions (Christian, 2026-10-27)

All recommendations in §5 accepted. The Typed Clojure fork's own files are
solely Christian's and may be relicensed and ported directly (upstream
Typed Clojure files remain EPL: ideas only). `../ChezScheme` updated to
upstream main (2026-10-23, fae51c27).

## 7. Next implementation steps

- **S1 runtime slice** (`klara/src`): core syntax (12 forms), world with
  immutable roots and one versioned publication protocol, basis-specific
  execution environments (no shared host namespace), the expander ported from
  v0 + X1 producing core terms, a T0 reference interpreter of K0 with
  reference handlers, and the specialization cache with guards and
  certificate-checked install. Tests: X1's criteria, R3 (deleting caches
  changes nothing), R4 (old/new versions coexist across forks).
- **S2 formal spec (X3)**: small-step semantics for the 12 forms with
  reference handlers in ansatz, Lean-compatible; compiled `step` run
  differentially against S1's T0 interpreter.
- **S3 first wandler idea** (after S1): map/filter/reduce fusion as a law-
  licensed rewrite with an ansatz certificate, installed through the
  specialization cache, with generic fallback on edit.
