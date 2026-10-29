# RFC 0006: Languages as world values

- Status: partially implemented (S13: first two ranked steps; remaining language interfaces are draft)
- Owner(s): Christian Weilbach
- Builds on: doc/architecture.md (portability and self-hosting), RFC 0003 (licences), RFC 0004 (canonical EDN), RFC 0005 (affine boundaries)
- Obligations: LG1–LG8 below

## Motivation

Klara must let users scope custom languages and formalisms — a Datalog
engine, a probabilistic modelling language, a numeric kernel language, an
agent sandbox — as first-class parts of a program, with reasoning tools
attached and without paying an interpretive layer for each. datahike's query
engine had to drop to Java host interop to be competitive; Klara should make
such a language fast inside the language, through staging, while keeping host
interop as an escape hatch.

## Proposal

**1. A language is an immutable EDN descriptor in the world**, versioned and
forkable like code (a Geschichte history interface is planned; no storage
adapter is implemented):

```clojure
{:language/id :rel/finite-v1
 :grammar grammar-id :binding binding-rules-id
 :readers {:sexp reader-id}             ; skins: presentation only
 :expand elaborator-id                  ; meaning by elaboration into Klara Core, or
 :reference interpreter-id              ; meaning by an interpreter (a Klara or ansatz definition)
 :observations observation-id           ; what counts as observable (values, effects, failures)
 :effects effect-signature-id
 :laws {law-id {:status :proved|:tested|:documented :evidence ...}}
 :model model-id :adequacy {:status ... :by ...}   ; optional formal model (§4)
 :analyses {:shape ... :cost ...}       ; removable predictors; never change meaning
 :maps #{translation-id}}
```

The semantic identity covers grammar, binding rules, reference meaning and
observation contract. Analyses and optimization policies version separately,
so removing an analysis never changes meaning. A skin alone is not a new
semantics: two skins of one program share its CodeId.

**2. Scoping.** `(with-language L form ...)` is lexical, resolved at expansion
under the recorded basis. `(interpret L program inputs)` selects a language
at run time, for explicitly supplied fragments only.

**3. The language graph.** Languages and maps form a directed multigraph,
with genuine partial orders only where they exist (core subsets by inclusion,
abstract domains by precision). Two extensions with conflicting rules need an
explicit composition, never an automatic join. Every map carries an
obligation and a licence:

| Map | Obligation |
|---|---|
| reader/skin → syntax | parsing, binding provenance, source positions |
| elaboration L → core | L's observations equal those of the elaborated program |
| compilation core → host | simulation: results, failures, divergence, effects |
| interpretation | defines the reference meaning |
| abstract interpretation | sound over-approximation |
| specialization (interpreter, fragment) → residual | `I_L(p, d) =obs= run(PE(I_L, p; A), d)` when assumptions A hold |
| approximate translation | metric and licence (RFC 0003) |

Laws transport only with an adapter and evidence.

**4. Proved languages.** Two routes:

- *Single source (preferred):* the interpreter is written once in ansatz
  (total, or fuelled), proved as far as practical, and **elaborated into Klara
  Core** so that staging can specialize it. Proofs travel with specialized
  code (s-m-n). The trust gap is one elaborator (ansatz → Klara Core), checked
  by translation validation or proved. The same route makes Klara's own spec
  the single source of its reference interpreter over time.
- *Dual (fallback):* a Klara interpreter as `:reference` plus an ansatz
  `:model`, related by an `:adequacy` licence (differential, like spec-diff,
  or proved).

**5. Boundaries** between an inner language L and the host M (EDN with
persistent-memory semantics is the common centre):

1. *L is a sublanguage of M* (same semantics, fewer capabilities): run
   natively in a fork with a restricted handler stack and authority set — no
   interpretive layer (the dvergr/spindel pattern for nested sci rooms). The
   sublanguage claim is itself a licence; host interop must go through the
   restricted handlers.
2. *L shares values but differs in semantics*: interpreter in Klara,
   specialized per fragment; checks only for values outside the shared subset
   (lifting is the identity on the shared subset).
3. *Foreign values*: explicit translation; staging may fuse conversions.

Boundary checks are staging guards: membership in the shared subset,
erased when established statically. Contracts carry full effect, failure and
blame traces, weaker observations only in named pure languages.

**6. Elaborating languages vs predictors.** Turnstile-style rule notation may
serve both, but an elaborator defines meaning while a predictor never does;
they stay distinct.

## First steps (ranked, from note O)

1. Syntax objects, local expansion and definition-context interfaces
   (extending the existing hygiene). **Built in S13:** syntax values,
   `quote-syntax`, full local expression expansion and lexical transformer
   definition contexts. Stop lists, module phases and variable-definition
   contexts remain open.
2. `syntax-parse`-style syntax classes and failure reports. **Built in S13:**
   `defsyntax`, `defsyntax-class`, attributes, datum literals, optional/repeated
   patterns and located failure data. Binding-sensitive literals, alternatives
   and richer syntax-parse attributes remain open.
3. Language descriptors and `with-language` / `interpret`.
4. Contracts and blame with monitor specialization (also RFC 0005 boundaries).
5. The ansatz → Klara Core elaborator (single-source route), first on the
   spec's own fragment, run through the spec-diff corpus.
6. Finite conjunctive Datalog as the first language: interpreter, staged
   evaluator with hand-written generators first. Gate: within 2× of a
   hand-written implementation with the same indices; compile break-even
   reported; datahike's indexed joins as baseline.

Not ported from Racket: the whole expander/module runtime, Typed Racket's type
hierarchy, deep wrappers on every value, global mutable instances.

## Obligations

| Id | Obligation | Status |
|---|---|---|
| LG1 | Language composition preserves binding (no capture across nested languages; a fork's transformer change does not affect another fork) | Tested for S13 syntax extensions and nested definition contexts (`syntax_test.clj`); general language composition open |
| LG2 | Cached expansion equals fresh expansion, including negative lookups and schema reads | Tested for S13 tracked world reads, transformer/class edits and canonical syntax identity (`syntax_test.clj`, `x1_test.clj`); host-state reads and persistent cross-fork caches open |
| LG3 | Erasing an analysis never changes meaning | Open |
| LG4 | Residual simulation: specialized fragment ≡ interpreted fragment (exhaustive on tiny inputs) | Open |
| LG5 | Boundary contracts survive optimization, with correct blame | Open |
| LG6 | Sublanguage execution cannot escape its handlers or authorities through host interop | Open |
| LG7 | Certificates cover actual execution (index normalization, schema, residual hash) | Open |
| LG8 | The ansatz → Klara elaborator preserves observations on the spec corpus | Open |

## Open questions

1. Who may publish a language descriptor into a shared world (authority over
   languages)?
2. Do language descriptors and module signatures (RFC 0007) share a
   versioning scheme?
3. The first non-Datalog language: the probabilistic modelling language
   (choose/observe with inference handlers), or an agent sandbox?
