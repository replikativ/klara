# E. Resources, bounded rationality, the learning runtime, physical awareness

Research note for Klara iteration 0 (2026-10-27). Aspect E of
`../00-design-space.md`. Paths are relative to `Development/`.
Status markers: **Holds** (argued, with enforcing code or an imported theorem),
**Conj** (plausible, unproven), **Open** (unknown, or the statement is not yet right).

## Position in brief: four disagreements

1. **No single quantale V carries cost, error and information value.** Each composes
   differently. Error composes with a Lipschitz factor (ε_{g∘f} ≤ ε_g + L_g·ε_f). The
   entropic grade composes multiplicatively through contraction coefficients. Cost composes
   by `+` in sequence and by `max` in parallel, which makes it a bimonoid rather than a
   quantale. Signature.md's quantale is correct for the ε component only. The grade layer
   should be a product of small algebras, each with its own composition law.
2. **Information value is not a grade.** By ESOP Prop. coinfo, what a branch adds is
   `U₂+S` *relative to what is already joined*. Two redundant branches are each worth v
   and together still worth v; two synergistic ones are worth more than the sum. A grade
   must be computable from the grades of the parts, and this quantity is not. It belongs
   in the policy (the proposal position) as an estimate, never in a type.
3. **Translation is lax-functorial in meaning and not functorial in cost.** Principle 5
   says "functorial". Fusion is the counterexample: `cost(T(g∘f)) < cost(Tg)+cost(Tf)`
   is the whole reason to compile across a boundary. Meaning is preserved up to a laxator
   (formalization.md D2). Cost has to be measured, because it cannot be derived from the parts.
4. **Fidelity does not separate from meaning the way placement does.** Halide and Legion
   schedules never change values (floating-point reassociation aside). A coarse model
   does change values. Klara should therefore split the decision: the *tolerance* ε is
   part of the program's contract (meaning), and the *choice* of fidelity that meets it
   is schedule. Raster's north star files fidelity under schedule
   (`raster/design/compiler-north-star.md:60-64`). That is right for the choice, and
   incomplete without the contract.

---

## 1. What prior docs and repos already settled

**Objective and cost vector.** The quantity to optimize is "grounding quality per unit of
compute" (`raster/design/compiler-north-star.md:35`). The cost vector includes
approximation error and information value. Fidelity is a schedule axis. Every
transformation carries an error model (`:55-69`, restated `:1186-1190`). The schedule
IR already lists device/mesh placement and fidelity level as schedule data (`:797-801`).
The pipeline order is fixed as legality → feasibility → analytic rank → measured rank,
and "a cost model may abstain" (`:818-822`). Learned cost models may replace parts of
ranking, "but the raw observations remain the source of truth" (`:1154-1156`). Learned
proposals compete in shadow mode and never bypass gates (`:1301-1302`). Autotuning is
plan data, not a source-language construct (`:1161`).

**Grades and the quantitative judgment.** The judgment is
`Γ;Δ ⊢ e : A ! φ ⟨E⟩ @ ε` with ε in a commutative quantale, and the binary calculus is
its 0-slice (`lambda-join/doc/probes.md:37-40`, `signature.md:3-8`). Forking is
grade 0 and joining carries the price (`probes.md:87-89`). W (evidence/weight) is split
by σ and never copied (`signature.md:28,45-47,95-97`). A join without π is a proposal
and must be a distinct term (`signature.md:166-168`). The trust ledger's levels are
enrichment choices over one calculus (`spine.md:80`, C-CAL-30). Several quantales sit
side by side, connected by Pinsker-type morphisms (`entropic.md:84-88`). That already
concedes disagreement 1. The per-constructor laxator rules are chain/Lipschitz,
oscillation, Grönwall, mass-weighted and likelihood-ratio (`towers.md:129-135`). D1–D5
and the owed theorems T1–T5 are stated in `formalization.md:76-119`. D5 (schedule:
an interleaving of propagate/join/abs) is the object an allocation theorem would
quantify over.

**Ledger rules.** Learned components sit only in the proposal/measure position
(C-LED-4, `spine.md:229`). An L1.5 certificate is `budget → bound` (C-LED-2,
`spine.md:227`; `obligations.md:103-105`). Variance is a cost term (C-LED-3). MLMC
gives an allocation theorem across fidelity levels (C-LED-6, `spine.md:231`). The
interface `(value, uncertainty, cost)` is adopted without PN algorithms (C-LED-8;
`obligations.md:114-116`). The hardware-keyed measurement cache is a W-ledger
(`formalization.md:166`), and schedule search is fiber search (`:163-164`).
"Improvement certification" is deliberately deferred (`obligations.md:127-131`).

**Talk.** Five moves: fork, ground, join, translate, rewrite. "Allocate is not a sixth
move: it is the policy that chooses among them under one budget. Purposes are constraints
on it, not prices" (`simm.is/worktrees/talk-mpi/.../index.html`, slide "To improve…").
The measurement rule `measure c when E[U(plan after c) − U(plan now)] > cost(c)` is
Russell–Wefald's value of computation. The licence ladder is exact / guarded /
approximate, "each licence ends in a checker the system cannot change". The ledger
`R_{t+1} = R_t + Π − κ − μ` is subject to a viability constraint.

**ESOP paper** (`lambda-join/papers/esop27-joins/main.tex`). The relaxed join
`x_ω = x₀ + Σω_i(x_i − x₀)` (:398-403). The naive-join error is `I(E₁;E₂|Θ)`, and a
branch's value is `U+S` (:441-465). Selection is a fork, so picking the best-looking
branch biases its estimate upward (:621-645). A join construct takes four declarations,
and its residual is an effect (:717-755).

**Implementation that already exists.** Foerster refuses to copy worlds holding
`:affine`, `:divisible`, unsettled `:linear` or `:shared` systems
(`foerster/doc/worlds.md:74-89`). This is a usage grading in practice. "A fork copies
state; it must not copy authority to spend": budgets are split evenly at fork and
resample, and unspent shares return on discard (`worlds.md:91-107`). That is σ on
money, running today. Steering is twisted SMC with a value estimate
(`foerster/src/org/replikativ/foerster/steer.cljc:1-30`). Wandler's planning JIT
re-plans on measured selectivity and is re-certified (`wandler/docs/JIT.md:13-39`). Its
hot-swap JIT deopts on guard failure, then pins after a cutoff (`:65-91`). Strict PGO
replay re-verifies instead of trusting the cached closure (`:110-122`). Its
float-reassociation flag is an explicit approximate lowering (`:166-169`). v0 emits a
content-addressed receipt per pass and has a ResourcePlan sidecar
(`lambda-join/doc/language.md:100-133`). The Truffle-derived bounded-reoptimization
budget is called "the W-ledger's spend ceiling" (`design-decisions.md:769-772`).

---

## 2. External survey (verified)

DOIs were checked against Crossref, and arXiv IDs against arxiv.org.

**Graded and resource types.**
- Granule: Orchard, Liepelt, Eades, *Quantitative program reasoning with graded modal
  types*, ICFP 2019. https://doi.org/10.1145/3341714. Graded modalities are indexed by
  user-chosen semirings, with several gradings coexisting. *Take:* a grade per resource
  kind, chosen à la carte.
- QTT: Atkey, LICS 2018, https://doi.org/10.1145/3209108.3209189; McBride, *I Got
  Plenty o' Nuttin'*, 2016, https://doi.org/10.1007/978-3-319-30936-1_12. Usage
  semiring {0,1,ω}; the 0 fragment is erased. *Take:* the usage grade for W/R. Foerster's
  copy grades already are this.
- Coeffects: Petricek, Orchard, Mycroft, ICFP 2014,
  https://doi.org/10.1145/2628136.2628160. Context requirements (resources, platform
  capabilities) tracked as coeffects. *Take:* "this code needs a GPU locale" is a flat
  coeffect.
- Fuzz: Reed and Pierce, ICFP 2010, https://doi.org/10.1145/1863543.1863568.
  Sensitivity types, `!_r A`, scale distances by r. *Take:* the Lipschitz factor L_g in
  the ε law is a sensitivity grade. The ESOP paper already cites this.
- Graded monads: Katsumata, POPL 2014, https://doi.org/10.1145/2535838.2535846.
  Effect gradings by a preordered monoid. Cost-as-effect fits here, not in a quantale.
- Quantitative equational theories: Mardare, Panangaden, Plotkin, LICS 2016,
  https://doi.org/10.1145/2933575.2934518. Already the planned home for `s =_ε t`.

**Amortized resource analysis.** Hoffmann, Aehlig, Hofmann, *Multivariate amortized
resource analysis*, TOPLAS 2012, https://doi.org/10.1145/2362389.2362393 (RAML).
Polynomial bounds are inferred by LP. *Assessment:* strong for first-order functional
code. For data-dependent simulation loops and device kernels the bounds are either
loose or unavailable. Klara should keep static cost bounds as an optional narrowing
rung, not as the cost model.

**Metareasoning.**
- Russell and Wefald, *Principles of metareasoning*, AIJ 49 (1991),
  https://doi.org/10.1016/0004-3702(91)90015-C. Value of computation, myopic
  approximation.
- Hay, Russell, Tolpin, Shimony, *Selecting computations: theory and applications*,
  UAI 2012, https://arxiv.org/abs/1207.5879. Shows metalevel decisions are
  intractable in general, and gives bandit-style VOC for MCTS. *Take:* no general
  optimality theorem should be expected. Seek theorems for instances.
- Lieder and Griffiths, *Resource-rational analysis*, BBS 43 (2020),
  https://doi.org/10.1017/S0140525X1900061X.
- Gershman, Horvitz, Tenenbaum, *Computational rationality*, Science 2015,
  https://doi.org/10.1126/science.aac6076.
- Ortega and Braun, Proc. R. Soc. A 2013, https://doi.org/10.1098/rspa.2012.0683.
  Information-processing cost as KL from a prior policy, which is the entropic grade
  applied to the policy.
- Anytime algorithms: Dean and Boddy, AAAI 1988,
  https://cdn.aaai.org/AAAI/1988/AAAI88-009.pdf; Zilberstein, AI Magazine 17(3) 1996,
  https://doi.org/10.1609/aimag.v17i3.1232. Performance profiles and contract versus
  interruptible algorithms. *Take:* a performance profile is exactly the L1.5
  `budget → bound` certificate. Zilberstein's composition of anytime modules is prior
  art for composing them.

**Probabilistic numerics.** Hennig, Osborne, Girolami, Proc. R. Soc. A 471 (2015),
https://doi.org/10.1098/rspa.2015.0142. MLMC: Giles, Oper. Res. 56 (2008),
https://doi.org/10.1287/opre.1070.0496. The optimal per-level sample count is
N_l ∝ √(V_l/C_l). This is the cleanest *theorem* about allocation across translate levels.

**Inference as effects.** Gen: Cusumano-Towner et al., PLDI 2019,
https://doi.org/10.1145/3314221.3314642. Generative-function interface, programmable
inference. Pyro: Bingham et al., https://arxiv.org/abs/1810.09538 (Poutine effect
handlers). Anglican: Tolpin et al., https://arxiv.org/abs/1608.05263 (CPS, checkpoints
at sample/observe). Foerster already sits in this line, with continuations replaced by
forkable worlds.

**Placement and locality.**
- Legion: Bauer, Treichler, Slaughter, Aiken, SC 2012,
  https://doi.org/10.1109/SC.2012.71. Logical regions plus privileges; the mapper decides
  placement and cannot affect correctness.
- Chapel: Chamberlain, Callahan, Zima, IJHPCA 2007,
  https://doi.org/10.1177/1094342007078442. The `locale` is a first-class value, and
  `on` clauses place work.
- Halide: Ragan-Kelley et al., PLDI 2013, https://doi.org/10.1145/2491956.2462176.
  Algorithm/schedule separation.
- Futhark: Henriksen et al., PLDI 2017, https://doi.org/10.1145/3062341.3062354.
  SOACs; the compiler owns placement.
- Exo: Ikarashi et al., PLDI 2022, https://doi.org/10.1145/3519939.3523446. Scheduling
  moved into user libraries, with every rewrite checked for equivalence.

*Take:* Legion's guarantee ("mapping affects performance, not results") is the right
v1 contract. Exo shows the scheduling library can be user code as long as each
primitive is checked.

**Learned optimization with certificates.**
- MLGO: Trofin et al., https://arxiv.org/abs/2101.04808. A learned inlining/regalloc
  policy that only chooses among legal decisions.
- TVM learned cost model: Chen et al., https://arxiv.org/abs/1805.08166.
- Ansor: Zheng et al., https://arxiv.org/abs/2006.06762.
- Translation validation: Necula, PLDI 2000, https://doi.org/10.1145/349299.349314;
  Alive2: Lopes et al., PLDI 2021, https://doi.org/10.1145/3453483.3454030; CompCert:
  Leroy, CACM 2009, https://doi.org/10.1145/1538788.1538814.
- Optimizer's curse: Smith and Winkler, Mgmt. Sci. 2006,
  https://doi.org/10.1287/mnsc.1050.0451.

*Take:* none of the learned-compiler systems separates *selection* evidence from
*claim* evidence. The tuned winner's reported speedup is measured on the data that
selected it.

---

## 3. Options with trade-offs

**Grade algebra.**

| Option | Gains | Costs |
|---|---|---|
| (a) One quantale V for everything | One theorem shape (signature.md) | Wrong composition for cost (seq `+`/par `max`) and entropy (multiplicative); information value is not compositional |
| (b) Static product of semirings, Granule-style, for all of usage, ε, cost | Checked at compile time; tidy | ε and cost depend on data and hardware; static bounds are loose or absent for simulators; a tax on every program |
| (c) **Split: static grades where they are structural, dynamic receipts where they are measured** | À la carte; zero cost when not opted in; measured truth stays the source (north star :1154) | Two mechanisms; dynamic ε is only as good as each laxator |

**Placement surface.**

| Option | Gains | Costs |
|---|---|---|
| (a) Compiler-owned placement (Futhark) | No surface | No user control; the city needs explicit residency (tables stay on device across scenarios) |
| (b) Locale values plus a user mapper (Chapel + Legion) | Explicit, testable; the mapper is a policy value | Mapper API design is real work |
| (c) Exo-style user scheduling library | Maximum control | Too much for v1 |

**Learning-loop architecture.**

| Option | Gains | Costs |
|---|---|---|
| (a) Ad hoc JIT heuristics (HotSpot) | Proven | Not replayable, not inspectable |
| (b) **Proposal → evidence → certificate, with content-addressed receipts** | Uses the language's own moves; replay re-checks certificates instead of re-running proposers | Receipt volume; certificate kinds must be designed |

---

## 4. Recommendation for Klara v1

### 4.1 The grade layer (option c)

**Static grades** live in the narrowing layer. They are opt-in, and removing them never
changes values.

| Grade | Algebra | Composition | Existing anchor |
|---|---|---|---|
| usage | {0,1,ω} semiring (QTT) | `+` at contraction, `·` at application | foerster copy grades, worlds.md:74-89 |
| binding time | lattice static ⊑ stable ⊑ dynamic | join | D2 |
| locale requirement | flat coeffect (set of capabilities) | union | north star :797 |
| sensitivity L | (ℝ≥0, ·) | multiply along composition | Fuzz; towers.md:131 |

**Dynamic receipts.** A value computed under a `with-ledger` handler carries
`{:value v :eps ε :cost c :evidence E :licence L}`. Without the handler, nothing is
allocated (obligation OE8).

- `ε` is a *vector* indexed by error model: worst-case metric, variance, KL. The
  per-model laws from towers.md:129-135 apply, with Pinsker-type maps between models.
- `c` is a cost vector over (time, bytes, memory-peak, energy, money). Sequential
  composition uses `+`; parallel composition uses `max` on time and `+` on the rest.
- `E` is the set of observation and measurement IDs consumed (signature.md §3).
- `L ∈ {L0, L1, L1.5, L2}` takes the weakest licence along the path.

**Through the five moves:**

| Move | ε | cost | E / budget |
|---|---|---|---|
| fork | unchanged (grade 0) | fork cost, O(1) for persistent state | E inherited; budget split by σ; requires usage ω or `freeze` |
| ground | unchanged, or reduced if the observation is used | acquisition cost | E ∪ {o}; **o linear: either fit or holdout, never both** |
| join | ε₁ ⊕ ε₂ ⊕ price(π); price = 0 if π holds, ≥ I(E₁;E₂\|Θ) if naive (ESOP) | merge cost | E₁ ∪ E₂, with the π check |
| translate | ε + laxator(T), measured or proved | measured, not derived | locale changes |
| rewrite | 0 (L0 proof) / 0 with guard cost (L1) / bound(budget) (L1.5) | guard plus deopt cost | certificate ID recorded |

Information value enters only as an argument to the policy. It is never part of a
receipt's claim.

### 4.2 Placement surface (minimal v1)

1. **`locale`** is a value describing a substrate: JVM heap, native arena, a GPU device,
   a remote node. It wraps raster's hardware descriptor with its provenance.
2. **`(translate T e)`** is the only way to cross substrates. `T` is a value (compile,
   marshal, offload, coarse-grain) with a declared error model. The result's receipt
   gains `laxator(T)` and measured cost. Exact compiles declare ε = 0. Raster's float
   reassociation declares ε > 0 and licence L2/L1.5 (JIT.md:166-169).
3. **`(with-mapper m body)`**: the mapper is a policy value that chooses locales and
   translations. Its contract, as in Legion: for every mapper the result equals the
   unmapped result up to the receipt's ε (OE1). Mappers are not part of the program's meaning.
4. **The tolerance is part of the contract**: `(within ε body)` states what the caller
   accepts. Any fidelity choice whose declared laxator exceeds ε is rejected before it runs.

There is deliberately no distributed-array type, no sharding syntax and no
user-visible schedule language in v1. Those stay in raster's plan IR, which Klara
reaches through `translate`.

### 4.3 The learning runtime

One loop, built from the language's own moves:

```
proposal   (fork; learned or heuristic; position: proposal)
  → evidence  (ground; measurements as W with provenance, keyed by hardware signature)
  → certificate (rewrite licence: L0 proof | L1 guard+deopt | L1.5 budget→bound)
  → adopt     (join into the running image; receipt published)
```

- **Receipts** are content-addressed EDN: program hash, proposal ID and proposer
  version, `:selected-on` evidence IDs, `:evaluated-on` evidence IDs, certificate,
  hardware signature, and budget spent. They are stored in Datahike. This extends
  v0's per-pass receipt (language.md:118-121).
- **Replay** re-checks the certificate and never re-runs the proposer. Wandler's strict
  PGO replay already does this (JIT.md:110-117).
- **Double counting is prevented by structure, not discipline.** (i) Measurements are W:
  they can be split, never copied. Pooling evidence across machines is a join that
  needs π, with the hardware signature as the base. (ii) Selection is a fork (ESOP
  Prop. selection). A receipt whose speedup claim uses evidence also in `:selected-on`
  is downgraded to "proposal": the runtime may use it to steer, but may not report it
  as a measured gain. (iii) Profiles that steer a rewrite are never cited as that
  rewrite's correctness evidence (C-LED-4).
- **Budgets** follow foerster's authority model (worlds.md:91-107): a reoptimization
  budget per code unit (the Truffle cap, design-decisions.md:769-772) is drawn from
  the session wallet and split by σ at fork.

### 4.4 Bounded rationality as a calculus: the smallest formal statement

A general optimality theorem should not be the goal; Hay et al. 2012 show the
metalevel problem is intractable in general. The smallest statement that is both true
and useful has three parts:

1. **Policy invariance (theorem target).** Let `D` be a schedule (formalization.md D5)
   generated by any policy over {fork, ground, join, translate, rewrite} under budget B.
   Then `run_D(e) =_{ε(D)} ⟦e⟧`, where `ε(D)` is the quantale composite of the receipts
   along D. Allocation can change cost and ε, and nothing else. This is T2 (graded
   confluence) restated for policies, and L14 is its L0 instance (signature.md:269).
2. **Budget conservation (theorem target).** Over any fork/resample/discard tree,
   granted = spent + returned. This is σ-linearity (L10) applied to money. Foerster's
   implementation runs it today.
3. **Optimality on instances (imported theorems, used as probes).** (a) Giles' MLMC
   allocation over a chain of translate levels (C-LED-6). (b) T5's persistence
   condition `ρ·e^{LΔt} < 1` for how often to ground. (c) Myopic VOC for single
   measurements (the talk's slide). Each is a probe: does the runtime's policy reach
   the known optimum on that instance?

Viability (`R_t ∈ 𝒱`) and purposes enter as constraints on the policy, not as terms of U.

### 4.5 Requirements from the Stuttgart simulation (`city-rstr`)

| # | Requirement | Source | Klara feature |
|---|---|---|---|
| R1 | Counter-addressed randomness: a draw is a pure function of (seed, person, index) | city-rstr/doc/architecture.md:66-69 | splittable keys; fork chooses *coupled* (same keys) or *independent* (fresh keys) |
| R2 | Paired baseline/scenario evaluation with common random numbers | doc/history/interactive-compute.md:24-29 | coupled fork as a first-class option; the basis for MLMC deltas |
| R3 | Forked numerical state must not share mutable primitive arrays or device buffers | interactive-compute.md:75-81 | usage grade on buffers; `freeze`/COW at the fork boundary; foerster's refusal extended to arrays |
| R4 | Stage products cached and invalidated per intervention | interactive-compute.md:31-47 | tracked, invalidatable staging (aspect C), with scenario identity in the cache key |
| R5 | One model run as expectation (no MC noise) or as sampler | architecture.md:97-98; doc/model.md:279-289 | `choose` handlers: enumerate/expectation vs sample, as a fidelity choice under `within` |
| R6 | GPU offload with a measured agreement (≈1e-13 relative, 0.5 s vs 3.6 s) | architecture.md:99-103 | `translate` receipts with measured ε and cost |
| R7 | Kernel bodies restricted to lowerable shapes | architecture.md:83-88 | a shaped narrowing rung that rejects with diagnostics, never silently falls back |
| R8 | One forked context per particle; MH re-executes from a site checkpoint | architecture.md:92-97 | foerster savepoints as the inference effect |
| R9 | An observation is either fitted or held out, "it cannot be both" | model.md:303-304 | **linear use of observations in E**, checked |
| R10 | Parameters traceable to measurement to receipt; as-of times on observations | model.md:489-491; interactive-compute.md:146-152 | evidence IDs with valid-time/ingest-time in receipts |
| R11 | Pooling two MH runs is a mixture (⊕), not a product join (⊗) | model.md:333-338; spine.md:77 | distinct `one/all` versus `join` |
| R12 | Routing and traces computed only on demand, for a viewport | interactive-compute.md:66-68 | demand-driven fidelity; the policy decides what to refine |
| R13 | 5 GB resident world; a ~40-minute full publish | architecture.md:49-52; interactive-compute.md:137-141 | memory and time as hard constraints in the budget vector, not as prices |

---

## 5. Obligations and falsifiers

| ID | Statement | Status | Falsifier |
|---|---|---|---|
| OE1 | Policy/mapper invariance up to receipt ε | **Holds** for wandler's L0 fragment (signature.md:268-269); **Conj** for Klara; **Open** for stateful hot swaps (JIT.md:99-108) | two mappers whose outputs differ by more than the receipts' ε |
| OE2 | Budget conservation over fork/resample/discard | **Holds** operationally (foerster); **Conj** formally (L10 Open) | a tree whose spent + returned ≠ granted |
| OE3 | Receipt ε covers realized error (T1 in practice) | **Conj** | coverage below the declared level (e.g. < 95%) in §6 |
| OE4 | Information value is not compositional, so it is not a grade | **Holds** (ESOP Prop. coinfo; the redundant/synergistic pair) | a decomposition rule for VOC valid on both redundant and synergistic branches |
| OE5 | Translation is lax-functorial in meaning and non-functorial in cost | **Holds** (fusion) | none expected; the point is to stop claiming functorial cost |
| OE6 | Receipts separating `:selected-on` from `:evaluated-on` remove the selection bias in reported speedups | **Open** (raster's cache does not record it) | held-out re-measurement shows no bias, which would make the field unnecessary |
| OE7 | MLMC allocation is optimal over a translate chain with the measured V_l, C_l | **Holds** (Giles); transfer **Conj** (C-LED-6) | the runtime's allocation loses to the best single level at equal budget |
| OE8 | À la carte: without `with-ledger`, overhead ≤ 2% | **Conj** | corpus benchmark above 2% |
| OE9 | Gradual guarantee for grades: erasing annotations preserves values | **Conj** | a program whose value changes when a grade is erased |
| OE10 | Persistence T5 as the grounding schedule | **Conj** (filter-stability import) | a bounded-error loop with ρe^{LΔt} ≥ 1 |

---

## 6. The smallest implementation experiment

**Allocation over translate levels on the city, with receipts.** About 300 lines of
Clojure in `city-rstr/dev`, with no Klara needed yet.

1. Write a `receipt` record and a `with-ledger` handler: a dynamic var and `binding`,
   with `(value ε cost evidence licence)` composed by the sequential and parallel laws.
2. Levels for the Milaneo-closure delta of visits on the small Stuttgart fixture:
   L0 = top-K gravity table with small K; L1 = larger K; L2 = exact dense kernel. Use a
   person subsample per level. Counter-addressed draws (R1) couple the levels for free.
3. Policies at equal budget: best single level; uniform split; Giles allocation from
   pilot V_l and C_l.
4. Measure the variance of the delta per unit cost (tests OE7), the coverage of receipt
   ε against the L2 reference (tests OE3), and the overhead with the ledger off (tests OE8).
5. Selection-bias side probe: pick the fastest of k raster schedules for the day kernel
   on run set A, then report the speedup on A versus a held-out run set B (tests OE6).

**Kill condition.** If Giles allocation does not beat the best single level by at least
the factor its own formula predicts, or coverage falls below 90%, then the dynamic-grade
design (4.1) is not earning its keep and should be cut back to static grades only.

---

## 7. Questions for Christian

1. **Is information value a grade or a policy input?** A grade must be computable from
   the parts. The ESOP paper's own Prop. coinfo shows a branch's value depends on what
   else has been joined. I propose keeping it out of types and receipts entirely and
   using it only to steer. Is there a use in your program where it has to be *checked*,
   not just estimated?
2. **Does a Klara program denote a value or a ball?** If `(within ε …)` is part of
   meaning, a coarse model that stays inside ε is a correct implementation, and the
   gradual guarantee ("annotations never change meaning") survives. If programs denote
   exact values, every fidelity change is a meaning change and needs its own licence.
   I recommend the ball. This decides how aspect A states adequacy.
3. **Which budget components are hard constraints and which are prices?** The talk puts
   purposes and viability as constraints. Concretely: is memory or a deadline a
   constraint (the city's 5 GB, a reply within 2 s) while money and energy are traded?
   The answer determines whether σ splits a vector at fork and whether the policy is a
   constrained optimizer or a scalar one.
4. Should mappers be user-programmable in v1 (Legion/Exo), or owned by the runtime with
   user hints only? I lean toward runtime-owned, with the mapper as a replaceable value
   for research.
5. Should learned decisions (receipts) persist and pool across machines and sessions in
   v1? This is where the π-on-hardware-signature rule becomes necessary rather than
   optional.
