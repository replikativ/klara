# A. Core calculus and its specification (research note, 2026-10-27)

Aspect A of `../00-design-space.md`. Status markers follow `doc/signature.md`:
**Holds** (argued or checked, with a pointer), **Conj** (plausible, unproven),
**Open** (we don't know, or the statement isn't right yet). Citations marked ✓
were checked against the primary source in this session. Citations marked (r)
come from memory and still need a check before they go into a paper.

**Disagreements first.** There are three, and the rest of the note depends on them.

1. **"MC substrate" as written is inconsistent with "W is not copyable".**
   Pavlović's book defines a monoidal computer as a monoidal category with a
   data service (copy/delete) *on every type* (*Programs as Diagrams* §2.5.1),
   in which every type is a retract of `P` (§2.3). MC I is stricter still:
   every type is a tensor power of the one universal type Ξ (Def. 4.1). Now
   suppose W were a retract of P (`e : W → P`, `r : P → W`, `r∘e = id`). Then
   `(r⊗r)∘Δ_P∘e` is a copy on W. So the table in `signature.md:23-31` cannot
   be the object set of one MC. The honest version is an MC of *data* (V, P,
   K-without-resources, H, T), a separate monoidal category of resources
   (W, R), and a link between them. That link is a new construction, and it
   becomes a new proof obligation.
2. **"λ vs MC" is not a real choice at the level of the core calculus.** A λ-calculus
   with quote, `run` and a definable specializer *already presents* an MC: its
   term model, with programs as the closed terms (MC I §4 examples; book
   §2.5.2). What the MC actually changes is which *equations* the spec adopts:
   no η on P, decidable equality on P, and `specialize` as a named operation
   rather than an encoding. Treat MC as the semantics' *vocabulary* and as the
   source of the s-m-n law. It is not a second calculus to mechanize.
3. **Making program identity observable can destroy the equational theory.**
   If Core programs can compare or hash *arbitrary closures*, contextual
   equivalence collapses to α-equivalence. This is Wand's fexpr result ✓
   [Wand 1998]. After that, no source-level optimization is sound. D1's
   "functions are program-values with hash identity"
   (`design-decisions.md:19-21`) is safe only if the identity is the hash of the
   *canonical expanded source*, taken before any optimization, and if
   inspecting it (`reify`) is a meta-level effect rather than a Core
   operation.

---

## 1. What our prior docs already settled

- **Semantic base.** We use a symmetric monoidal CD-category in which only some
  objects have copy/discard, together with MC structure. It is explicitly not
  CCC (`signature.md:17-47`, `:278-288`). `run` is a surjection, and its fibers
  carry certified swap and content addressing (`signature.md:37-43`;
  `lambda-v.md:15-50`). The reason given is the MC's lack of a function space:
  you quote instead of currying (`lambda-v.md:25-27`).
- **D1 (firm).** The core forms include `quote`/`run`/`specialize`, and
  extensional behaviour is a Tier-M contract on `IFn` (`design-decisions.md:10-23`).
- **D2 (firm).** Hygiene uses scope sets, expansion is an effect selected by
  handler stacks, and phases become the lattice static ⊑ stable ⊑ dynamic
  (`design-decisions.md:25-68`).
- **D8.** The λ∨ operator set is the effect signature and handler stacks are
  the interpreters. The OCaml model applies: handlers are dynamic, the type
  system plays no part, and unhandled effects are re-performed outward.
  Koka's clause kinds are declared on the handler
  (`design-decisions.md:396-432`). In `lambda-v.md:131-153` split, join,
  branch, abs, sample and observe are all effects, and the trust ledger
  classifies *stacks*.
- **The λ∨ calculus as a rewrite system**, Verse-shaped, with choice in the term.
  Confluence up to equality of distributions is the headline result and is
  **Open** (`signature.md:172-203`; `obligations.md:8-26`). Host calls are
  opaque, and confluence is stated only for the host-free fragment
  (`obligations.md:24-26`).
- **World and state.** There is one persistent world value. A fiber pins a
  basis, and merge is a π-checked join of deltas (`state.md:12-37`).
- **Bootstrap.** A small interpreter of the core forms is the universal seed
  (`bootstrap.md:108-118`). The kernel stays outside the compiler
  (`bootstrap.md:120-125`).
- **Mechanization plan.** Redex first, then a Clojure twin, then ansatz
  (`formalization.md:121-128`). O3 (adequacy of partial-CPS) was named the
  right first mechanized result (`obligations.md:53-67`).
- **Code as it exists today:**
  - `redex/lambda-join.rkt:33-73,236-262`: λ + let/if + split/join/joinp/dup/push/hist, plus a `mass` metafunction.
  - `lean/LambdaJoin/Core.lean`: a first-order fragment (num/obs/pair/split/join/let). Preservation, progress and no-double-counting are proved (`:425,:505,:578`), with no `sorry`.
  - `v0/src/v0/analyze.clj:113-155`: the analyzer ops are 22 Clojure special forms.
  - `v0/src/v0/kernel.clj:26-43`: **Kernel-v0** already contains literal, local, resolve, let, if, do, program, closure, run, vector/map/set, apply-op, perform, handle and host-op.
  - Two caveats about Kernel-v0. Its `:handle` merges a capability map into a dynamic context (`kernel.clj:379-386`), so it gives only *tail-resumptive, no-continuation* handlers. And the lowering rejects named, multi-arity and variadic fns as well as loop/letfn (`kernel.clj:754-762`, `:792`).

## 2. External survey (primary sources)

**Monoidal computer.**
- Pavlović, *Monoidal computer I: Basic computability by string diagrams*, Inf. & Comp. 226 (2013) 94–116, [arXiv:1208.5205](https://arxiv.org/abs/1208.5205) ✓.
  - Def. 3.1: a data service is copy, delete and filter, with the copy/delete forming a commutative comonoid.
  - Def. 4.1: the universal type Ξ generates all types. Universal evaluators `u` exist such that every computation has a program (eq. 11). Partial evaluators `s` satisfy eq. 12, the s-m-n law.
  - The paper notes that `⌜{p}⌝ = p` usually fails. Only the strongly extensional computers satisfy it.
- Pavlović, *Monoidal computer II: Normal complexity by string diagrams*, [arXiv:1402.5687](https://arxiv.org/abs/1402.5687) ✓. It grades by complexity. Relevant to us: it says time and space are "normal" measures, while *average and randomized complexity are not*. That matters for any cost grade over sampling programs.
- Pavlović & Yahia, *Monoidal computer III: A coalgebraic view of computability and complexity*, CMCS 2018, LNCS 11202, [arXiv:1704.04882](https://arxiv.org/abs/1704.04882) ✓. Having interpreters and specializers is equivalent to having a universal state space that carries weakly final state machines. **This is the bridge to operational semantics**: a small-step semantics is a state machine.
- Pavlović, *Programs as Diagrams: From Categorical Computability to Computable Categories*, Springer 2023, [arXiv:2208.03817](https://arxiv.org/abs/2208.03817) ✓. §2.5.1 defines an MC by three conditions: (a) a data service on *every* type, (b) a program type P with *decidable equality*, (c) evaluators for all A, B. §2.3 proves that types are retracts of P, and §2.3.2 treats types as idempotents. Conditionals are lazy branching (§3.6.1), which `gatlab-clj/doc/programs-as-diagrams.md:69-81` already uses.

**Turing categories.**
- Cockett & Hofstra, *Introduction to Turing categories*, APAL 156 (2008) 183–209 ✓ ([PDF](https://www.di.ens.fr/users/longo/files/Cockett-TuringCateg.pdf)).
  - The setting is a *cartesian restriction category*. It has a Turing object A, with every object a retract of A, and a universal application τ for which every `f : Z×X → Y` has an index `h : Z → A`. The recognition theorem says a single Turing morphism `A×A → A` suffices ([summary](https://golem.ph.utexas.edu/category/2019/08/turing_categories.html) ✓).
  - Turing categories correspond to PCAs. Cockett & Hofstra, *Categorical simulations*, JPAA 214 (2010) makes this an equivalence (r).
- **I found no published theorem relating MC and Turing categories.** MC III cites Turing categories only as related work ✓. My reading: in the cartesian, deterministic case the two coincide up to presentation, since an MC with a cartesian data service is a Turing category with Ξ = A. MC drops cartesianness, so non-natural copy can model nondeterminism and partiality without restriction structure. That is **Conj**, and is worth one lemma if we cite both.

**Effects and handlers.**
- Plotkin & Power, *Algebraic operations and generic effects*, ACS 2003 (r).
- Plotkin & Pretnar, *Handlers of algebraic effects*, ESOP 2009 (r), and *Handling algebraic effects*, LMCS 9(4) 2013, [arXiv:1312.1399](https://arxiv.org/abs/1312.1399) (r).
- Bauer & Pretnar, *Programming with algebraic effects and handlers*, JLAMP 2015 (Eff) (r).
- Leijen, *Type directed compilation of row-typed algebraic effects*, POPL 2017 (r), and Xie & Leijen, *Generalized evidence passing for effect handlers*, ICFP 2021 (r).
- Sivaramakrishnan et al., *Retrofitting effect handlers onto OCaml*, PLDI 2021 (r). Its handlers are one-shot.
- Forster, Kammar, Lindley & Pretnar, *On the expressive power of user-defined effects*, ICFP 2017 / JFP 2019, [arXiv:1610.09161](https://arxiv.org/abs/1610.09161) ✓. Handlers, monadic reflection and delimited control macro-express each other when typing is ignored. They separate only under typeability-preserving translations, and even that separation breaks under polymorphism.
- For PPLs: Ścibior, Kammar & Ghahramani, *Functional programming for modular Bayesian inference*, ICFP 2018 (r), where inference is a stack of transformers or handlers over a reference semantics. Pyro and Edward2 use effect-handler stacks (r). Staton et al., LICS 2016, gives the s-finite-kernel semantics with `score` (r).

**Specification exemplars.**
- Milner, Tofte, Harper & MacQueen, *The Definition of Standard ML (Revised)*, MIT Press 1997 (r). Its known defects are catalogued by Kahrs and later Rossberg (r).
- Lee, Crary & Harper, *Towards a mechanized metatheory of Standard ML*, POPL 2007 (r). They elaborate the surface into a small internal type theory and mechanize *that* in Twelf.
- Kumar, Myreen, Norrish & Owens, *CakeML: a verified implementation of ML*, POPL 2014 (r), and Owens et al., *Functional big-step semantics*, ESOP 2016 (r). In the latter the semantics is an executable clocked interpreter in HOL4, and it serves as both spec and oracle.
- Matthews & Findler, *An operational semantics for Scheme*, JFP 18(1) 2008 (r). The R6RS appendix is a Redex model. Klein et al., *Run your research*, POPL 2012, found bugs in published semantics by random testing in Redex (r).
- Haas et al., *Bringing the web up to speed with WebAssembly*, PLDI 2017 (r).
- Watt, *Mechanising and verifying the WebAssembly specification*, CPP 2018 (r). Its Isabelle mechanization found spec errors before 1.0. Watt et al., *Two mechanisations of WebAssembly 1.0*, FM 2021, adds a second (r).
- Youn et al., *Bringing the WebAssembly standard up to speed with SpecTec*, PLDI 2024, DOI [10.1145/3656440](https://doi.org/10.1145/3656440) ✓. **One DSL source generates the typeset rules, the prose pseudocode and an interpreter.** That interpreter passes 100% of the applicable Wasm 2.0 tests, and the work found 10 errors in 5 proposals.

**Adjacent results we rely on.**
- Wand, *The theory of fexprs is trivial*, LASC 10(3) 1998 ✓.
- Davies & Pfenning, *A modal analysis of staged computation*, JACM 2001 (r). This is the typed λ-world's version of quote/run, if a narrowing layer ever wants one.
- Benton, *A mixed linear and non-linear logic*, CSL 1994 (r). The LNL adjunction is the standard way to join a cartesian and a linear world.
- Fritz, *A synthetic approach to Markov kernels…*, Adv. Math. 2020, and Cho & Jacobs, MSCS 2019 (r). These cover CD and Markov categories. Our "copy on some objects" is close to their setting, and Christian knows it.
- Augustsson et al., *The Verse calculus*, ICFP 2023 (r).
- Carneiro, *Lean4Lean*, [arXiv:2403.14064](https://arxiv.org/abs/2403.14064) (r).

## 3. Options with trade-offs

**Foundation.**

| | λ-calculus / CCC | Pavlović MC | Turing category |
|---|---|---|---|
| Program identity | quotiented away by β/η | primitive (P, fibers of `run`) | primitive (indices into A) |
| Partiality | needs domains or a lift | built in (data service not natural) | restriction structure |
| Non-copyable objects | no (cartesian) | **no, as defined**: every type has a data service (Disagreement 1) | no (cartesian) |
| Specialization | an encoding | an axiom (eq. 12) | derivable from indices |
| Mechanization prior art | very large | essentially none | small (realizability in Coq/Agda) |
| Operational link | standard adequacy (Plotkin 1977) | MC III: machines ⇔ MC | PCA ⇔ Turing category |

None of the three gives us W/R for free. **What we need is a two-world structure.** One world is a CD-category 𝒟 whose copyable part contains an MC 𝒞 (V, P, H, T, resource-free K). The other is a monoidal category ℒ of resources (W, R) acted on by 𝒞, in the LNL style: `run_Δ : P ⊗ A ⊗ Δ → B ⊗ Δ`, so that programs are copyable data while the resources they act on are not. This matches `signature.md`'s judgment `Γ ; Δ ⊢ e` (`:103-113`) and the rule "forkable = copyable" (`00-design-space.md:49`).

**Effects.**
- **(E1) Algebraic effects + deep handlers in Core.** perform/handle is primitive, and choose, observe, factor, fork, join, expand, world-define and host are operations. Each operation's *meaning* is fixed by a **reference handler**. Inference algorithms and JIT realizations are other handlers, and they owe a correctness theorem relative to the reference.
- **(E2) Smaller core with delimited control** (shift/reset, or prompts). Handlers are then derived by elaboration. Forster et al. show this costs no expressiveness in an untyped core. The cost is that "a handler stack is the interpreter" stops being a syntactic object the ledger can classify (D8, `lambda-v.md:131-153`). We would also need to re-derive handler-level laws.
- **(E3) No control in Core.** Effects become a monad by elaboration (free monad or interaction trees). This is clean for proofs (Xia et al. POPL 2020 is in `lit/`), but it defeats zero-overhead hosting, because everything ends up CPS'd.

How λ∨ fits under E1. λ∨'s rewrite rules (SPLIT-ASSOC, JOIN-DIST, …) rewrite *under* choice and are order-free, while handlers are sequential and context-directed. These two pictures meet if the λ∨ laws are taken as the **equational theory of the reference handler for choose/join**: λ∨ terms are the free model, and the measure semantics is the quotient. Redex then checks the laws, and Core's small-step semantics with the reference handler is one strategy for them. Confluence (O1) becomes "every handler strategy agrees with the reference distribution".

**Spec structure.**
- *SML style* (rules on paper only): brittle, as the defect catalogues show.
- *R6RS style* (Redex as the spec): executable and good for random testing, but no proofs.
- *CakeML style* (functional big-step in a prover): one artifact is both spec and oracle. Handlers fit awkwardly without a CPS'd interpreter.
- *Wasm style* (prose + formal + reference interpreter + test suite, now generated from a single source): best practice. It needs a single source of truth.

## 4. Recommendation: Klara Core v1

**Foundation.** The spec is a λ-calculus with call-by-value small-step semantics. Its MC structure is stated as theorems about the spec, not as axioms of it. The semantic target is the two-world 𝒞/ℒ structure above. In short: MC as interface, λ as definition.

**Forms (12).** Locals are de Bruijn indices.

```
e ::= x                         local
    | (quote d)                 datum literal — V, including code-as-data
    | (fn [x…] e)               program value (closure) — element of P
    | (e e…)                    application = run of a closure  {p}a
    | (let [x e] e)
    | (if e e e)
    | (letrec [(f (fn …))…] e)  recursion; loop/recur, letfn, named fn elaborate here
    | (resolve id)              read the pinned world (global ref)
    | (prim op e…)              Tier-L algebra op from the operations signature
    | (perform op e…)           effect operation
    | (handle e h)              deep handler: h = {return (fn [x] e), op (fn [v k] e) …}
    | (specialize e e)          s-m-n on P; reference meaning = closure formation
```

Everything else becomes an effect or elaborates away:

| Today's form | Becomes |
|---|---|
| `def` | `(perform :world/define id v)`, handled by the REPL/world handler (state.md's transactor) |
| `throw`/`try` | an `:exn` operation and its handler |
| `set!`, `new`, `.` | `(perform :host/… )` with a contract, like Kernel-v0's `host-op`; the outermost handler is the host |
| `case*` | `if` + `prim` |
| `do`, vector/map/set constructors | `let` and `prim` |
| `eval` | `run ∘ analyze`, where `analyze` is the `:expand` operation (D2) and returns P |

So `quote` yields V and only expansion yields P. Closures can't be reified back into source inside Core, which is the defence against Wand. `specialize` is in Core so the s-m-n law is a spec-level equation. Its reference meaning is the trivial Kleene construction: `(specialize p m)` ≡ `(fn [n] (p m n))`. Real specializers are certified moves within the fiber.

**Continuations.** One-shot by default. Multi-shot resumption is a capability, available only when the captured context has an empty linear footprint (no R or W). That restriction *is* "forkable = copyable" for K. It makes the K row of `signature.md:27` conditional instead of ✔.

**Judgments.**
1. `⊢ e wf`: scoping only. The core is dynamic.
2. `e ⟶ e'`: CBV small-step with evaluation contexts `E`. The handler rule is `handle E[perform op v] h ⟶ h.op(v, λy. handle E[y] h)` when `E` does not handle `op`. An unhandled operation at top level is stuck, and stuck is a *named* error.
3. Reference handlers:
   - `H_world`, for define/resolve-basis.
   - `H_host`, an oracle parameter, so theorems are stated *for all* host oracles satisfying a contract.
   - `H_meas`, for choose/observe/factor, into finite discrete subdistributions in v1. Mathlib's kernels are available through ansatz for later.
   - `H_fork`, for split/join, carrying λ∨'s π premise.
4. Narrowing (layer 2, not Core): `Γ ; Δ ⊢ e : A ! φ` from `signature.md:103`, with the gradual-guarantee obligation.

**Adequacy statement (proposed).** Fix a host oracle ω. Let `⟦e⟧_ω` be the denotation into 𝒟, and `obs_ω(e)` the subdistribution over values reached by `⟶*` under the reference handlers.

> **A1 (computational adequacy).** For closed `e` of observable sort, `⟦e⟧_ω = obs_ω(e)`.
> **A2 (MC structure).** The interpretation carries an MC on the copyable part:
> (i) eval-quote: `⟦run⟧ ∘ (⌜e⌝ ⊗ id) = ⟦e⟧` for every program value `e` (MC I eq. 11), with `⌜·⌝` injective modulo α (the content hash);
> (ii) s-m-n: `⟦run⟧ ∘ (⟦specialize⟧ ⊗ id) = ⟦run⟧` (MC I eq. 12);
> (iii) the fibers of `⟦run⟧` contain the contextual-equivalence classes but need not equal them. A certified swap uses a *sound* relation, such as a logical relation or a kernel proof, not full abstraction.
> **A3 (resources).** Linear-footprint terms interpret in ℒ, and `run_Δ` is natural in Δ but not copyable in Δ.

A1 is classical in shape (Plotkin's LCF adequacy, plus a probabilistic version over discrete distributions). A2(i)–(ii) are near-trivial for the term model. The content is that they hold *in a model where P is syntax modulo α while the extensional shadow is non-trivial*. A3 is the new part.

**Spec structure.** Follow the Wasm/SpecTec shape, with one source:

1. **The source is Lean-4-compatible definitions written in ansatz.** It contains the syntax inductive, `step : Config → Option Config` as a *total function*, and `Step` as its graph. Watt's Isabelle work has the same relation + interpreter pair.
2. **The reference interpreter is that `step`, compiled by ansatz to Clojure.** ansatz `a/defn` compiles kernel-checked functions to ordinary Clojure; see the probe below. Spec and oracle are then the same artifact, which is the CakeML trick without the handler awkwardness.
3. **Redex stays** as the exploratory, random-testing model for λ∨ rewrite laws (R6RS lesson). It is differentially tested against (2).
4. **Prose** is generated from or checked against (1). A rule table per form is enough for v1.
5. **The corpus** (`../clojure-conformance`, the v0 corpus) is the conformance suite, and it runs against (2).
6. **katzen/GAT** is the *readable categorical spec* of the target structure: SMC, CD, data service, the MC equations (11) and (12). It also provides a model-checking harness, with backends as models via `katzen.ansatz.export`. It is not the spec of the operational semantics; see F7.

## 5. Proof obligations and falsifiers

| # | Statement | Status | Falsifier / note |
|---|---|---|---|
| A-O1 | Type safety of Core v1 under reference handlers: progress modulo *named* stuck states (unhandled op, host contract violation) + preservation of well-scopedness | **Conj** | Standard. Kernel-v0 is evidence. Falsified if a host-op can reach a stuck state that isn't named. |
| A-O2 | A1 computational adequacy, discrete fragment | **Conj** | Known technique. Falsified if `H_meas` needs non-discrete measures before v1 ships. |
| A-O3 | A2(i)–(ii): eval-quote and s-m-n with trivial `specialize` | **Conj** (near **Holds**) | Falsified if the de Bruijn hash isn't injective modulo α on expanded code. Scope-set nondeterminism is exactly that risk (`design-decisions.md:42-44`). |
| A-O4 | Two-world 𝒞/ℒ construction exists, with W, R excluded from 𝒞's retracts and `run_Δ` natural | **Open** | **New.** Falsified if any Core operation lets a W value flow into a P-encodable position, since copy then becomes derivable (Disagreement 1). |
| A-O5 | Observable equality on closures is α-equality of canonical expanded source; `reify` is an effect | **Conj** | Falsified (via Wand) if Clojure compatibility forces `(= f g)` to see post-optimization identity, or forces closure-to-source reification into Core. |
| A-O6 | Multi-shot `k` is admissible iff the captured linear footprint is empty | **Conj** | Falsified by a PPL benchmark (SMC, enumeration) that needs to copy a continuation holding an R. If so, the R must be frozen at the fork boundary, and that is aspect B. |
| A-O7 | The λ∨ laws (SPLIT-ASSOC, JOIN-DIST, RESAMPLE) are sound for `H_meas`/`H_fork` | **Conj** | Redex checks them on random terms (`redex/test.rkt`). This is O1/L6 restated, and stays **Open** for the full rewrite system. |
| A-O8 | Kernel-v0 `:handle` (tail-resumptive) = Core `handle` restricted to clauses that call `k` exactly once, in tail position | **Conj** | This is the Koka fast-path theorem. Falsified if a v0 corpus program relies on a non-tail resume. |
| A-O9 | Elaboration of the 22 analyzer ops into Core preserves behaviour on the corpus | **Open** | Differential test. Note that Kernel-v0 currently rejects loop/letfn/named/variadic fns. |
| A-O10 | MC (cartesian case) ≅ Turing category with Ξ = A | **Conj** | Only needed if the paper cites both. A lemma, not core work. |
| F7 | GATs can state the *operational* semantics | **Holds (negative)** | GATs are equational. "Every f has a program" (eq. 11 surjectivity) is ∃-quantified, and `⟶` is a relation, so neither is a GAT axiom. GATs state the *structure*, and the adequacy theorem lives in Lean. Also, katzen's `ThSymmetricMonoidalCategory` (`gatlab-clj/src/katzen/stdlib/core.clj:83-127`) declares operations but no coherence axioms yet. |
| F8 | ansatz can host the spec | **Holds (probe)** | See §6. Falsified if porting `Core.lean` needs features ansatz lacks (mutual blocks in the surface, `simp` on arithmetic: the README marks `simp +arith` a known gap). |
| F9 | Lean proper re-checks the ansatz development | **Conj** | The `ansatz.surface.lean` emitter exists. Untested on a relation-heavy development. |

## 6. Existing assets and the smallest step

**Assets.**
- `v0/src/v0/kernel.clj` is already about 80% of Core v1. It has the op schema as EDN, the `fold` model interface, a reference model, and perform, handle and host-op. It is missing letrec, specialize, real continuations, and the elaboration of loop, letfn, def and try.
- `lean/LambdaJoin/Core.lean` is a proved first-order λ∨ fragment, and the template for the `Step`/`WT` style.
- `redex/lambda-join.rkt` provides the law models.
- ansatz offers inductives (indexed, Prop-valued), `cases`, `induction`, `simp`, `omega`, `grind`, compilation to Clojure, and a Lean emitter.
- `katzen.ansatz.export` turns a GAT into a CIC structure.
- `partial-cps` ioc is the validated form list (O3).

**Probe run for this note (ansatz, `clojure -M -i`, about 60 s).**
- Defined a 5-constructor syntax inductive `Tm` (var/lit/lam/app/perf).
- Defined an indexed Prop `IsVal`.
- Defined a recursive `tsize`, which compiled to a plain Clojure `fn` using tagged vectors.
- Defined an indexed Prop `Step` with recursive premises (congruence rules).
- Proved `Step (lit n) t → False` by `cases`.
- Proved `1 ≤ tsize t` by `cases`, `simp`, `omega`.

All of these were kernel-checked. This is the basis for F8 = Holds. The probe did *not* test substitution lemmas, mutual blocks, or the Lean export.

**Smallest step that tests the recommendation (about 1 week).** Write **`klara-core-v1` in ansatz**:
1. a de Bruijn `Tm` with the 12 forms;
2. `step` as a total function with deep handlers via evaluation-context decomposition;
3. `Step` as its graph;
4. A-O1 (progress/preservation for well-scopedness);
5. the compiled `step` run as an interpreter over the Kernel-v0 corpus, differential against `v0.kernel/eval-term`.

Decision rules:
- **Kill or rethink** if step 4 takes more than 2× the effort of the corresponding `Core.lean` proofs. In that case mechanize in Lean proper and keep ansatz as the re-checker.
- **Kill or rethink** if the compiled interpreter is too slow to run the corpus.
- **Confirms the recommendation** if the corpus agrees and A-O8 holds on it.

Then port `Core.lean`'s footprint theorems into the same development, which is A-O4's first slice.

## 7. Questions for Christian

1. **Which copy structure is primary?** Pavlović's MC puts copy on *every* type. Your table removes it from W and R. I propose "an MC of data, acting on a linear world of resources". This is like Benton's linear/non-linear split, and close to how a Markov category separates deterministic from stochastic maps. Is that the reading you intended for D1? Or did you mean W to be inside the MC with a copy that is merely *forbidden* by the type layer? The second option is cheaper to state, but A-O4 then becomes a typing theorem rather than a structural one.
2. **Should program identity be observable in Core?** If `(= f g)` on closures sees code identity, compilers can't optimize function bodies without changing meaning (Wand 1998). I propose that identity is the hash of the expanded source, frozen before optimization, and that looking *inside* a closure is a reflective effect. Does that keep everything you need for content-addressed defs and certified swap? It costs that `(= (fn [x] (+ x 1)) (fn [x] (+ 1 x)))` is `false`, deterministically.
3. **Should multi-shot continuations be in Core?** Your PPL use cases want them: enumeration, SMC resampling, the λ∨ `split` on K. OCaml deliberately ships only one-shot, because multi-shot interacts badly with resources and GC. I propose multi-shot only when the captured computation holds no resources. Is there an inference algorithm you care about that needs to fork a continuation *holding* a live resource, such as an open datahike transaction? If so, freezing at the fork boundary (aspect B) has to carry it.

Smaller ones:
- Is finite discrete `H_meas` acceptable for v1, with Mathlib kernels later?
- Should `specialize` be in Core at all, or a library over `fn` until the staging aspect (C) lands? Keeping it makes the s-m-n law a spec equation, at the cost of one form.
