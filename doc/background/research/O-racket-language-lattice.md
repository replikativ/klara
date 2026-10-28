# O. Racket and Klara's language lattice

Research proposal for Christian Weilbach, 2026-10-28. **Recommendation:** make a language an inspectable, versioned semantic package, usable both as a scoped notation and as an interpreter value. Make translations, analyses and specialization explicit maps with different obligations. Racket supplies the language-building interfaces; Klara supplies world tracking, fork discipline and licensed residual execution.

## 1. Scope, evidence and existing commitments

Local citations use `K:` = `/home/christian-weilbach/Development/klara/`, `R:` = sibling `racket/`, and `D:` = sibling `datahike/`. Racket was inspected at `9fa53a48ad0d4d9cd0d858d89b9f3c0758f4b1a6`; Klara and Datahike citations describe their working trees. Package sources absent from the Racket checkout are identified through upstream links, not invented local paths. No runtime performance experiment was conducted for this note.

This extends C's assumption-indexed staging and cache obligations, F's separation of matching semantics from compilation strategy, I's Chez/pattern hybrid, and J's product of abstract domains (`K:doc/background/research/C-staging.md:262`, `F-stdlib-matching-laziness.md:41`, `I-chez-pattern.md:325`, `J-type-systems-as-predictors.md:380`). It does not reopen those choices. RFC 0005 already decides lexical borrows, opt-in ownership, a Klara checker and JVM-first emission (`K:rfc/0005-affine-regions.md:264`).

Status matters: `specialize` has partial-application reference semantics; the general interpreter-to-compiler route is research (`K:doc/architecture.md:175`). Code values work, but macros still receive plain data, and `run` currently evaluates generated terms in T0 (`K:doc/guide/05-staging.md:287`). The compilation guide documents a tested conservative emitter, excluding ambient host/staging calls and unknown higher-order calls (`K:doc/guide/08-compilation.md:78`). These newer descriptions supersede stale “no IR passes” statements elsewhere. Everything proposed below is design, not an implemented API.

## 2. What Racket actually contributes

### Languages as libraries and binding infrastructure

The pipeline is:

```text
bytes -- #lang-selected reader --> syntax/module declaration
      -- module-language bindings + expansion --> expanded core
      -- module/phase compilation --> linklets --> runtime
```

`#lang` selects reader machinery; the resulting module's language supplies initial bindings. A module language can control module bodies, application and literals through `#%module-begin`, `#%app` and `#%datum`. This is more powerful than textual preprocessing: even ordinary-looking application can elaborate differently. The reader protocol exposes `read`, `read-syntax`, wrappers and tool information (`R:racket/collects/syntax/module-reader.rkt:36`); the expander inserts implicit application (`R:racket/src/expander/expand/main.rkt:94`) and requires the module language's body binding (`R:racket/src/expander/expand/module.rkt:710`).

Phases distinguish bindings used by executing programs from those used by transformers. `begin-for-syntax` advances the phase; `for-syntax` imports shift dependencies accordingly. They are relative phase levels, not simply two global moments called compile time and runtime. The implementation recursively expands phase-shifted bodies and runs available modules at the incremented phase (`R:racket/src/expander/expand/module.rkt:856`). A runtime invocation of expansion still needs this distinction. Klara should keep phase separate from C's static/stable/dynamic grades and from world version.

Flatt's [*Binding as Sets of Scopes*, POPL 2016](https://www-old.cs.utah.edu/plt/publications/popl16-f.pdf) explains identifier binding through scope sets rather than expansion-history renamings. The local resolver searches applicable subsets and detects ambiguity (`R:racket/src/expander/syntax/scope.rkt:958`). Klara already uses scope sets; the missing gain is an explicit syntax-object API with source locations, binding-aware equality and tracked local expansion. Canonical identity must not depend on freshly allocated scope numbers.

Flatt, Culpepper, Darais and Findler's [*Macros that Work Together*, JFP 2012](https://www.cs.tufts.edu/~nr/cs257/archive/matthew-flatt/macros-work-together.pdf) supplies the complementary API lesson: partial expansion, definition contexts and compile-time bindings let independently written extensions cooperate. Tobin-Hochstadt et al.'s [*Languages as Libraries*, PLDI 2011](https://www2.ccs.neu.edu/racket/pubs/pldi11-thacff.pdf) demonstrates a typed language and optimizer implemented through that interface. Felleisen et al.'s [*A Programmable Programming Language*, CACM 2018](https://cs.brown.edu/people/sk/Publications/Papers/Published/fffkbmt-programmable-prog-lang/) makes the broader case for language construction as ordinary programming supported by common tools.

`syntax-parse` adds reusable syntax classes, attributes, literal-binding recognition, constraints and contextual errors. Classes become parser definitions plus compile-time descriptions (`R:racket/collects/syntax/parse/private/parse.rkt:55`); failure rendering carries descriptions and roles (`R:racket/collects/syntax/parse/private/runtime-report.rkt:676`). Porting this *interface* would let a query report an unsafe head variable at its source location rather than fail in a generated join. Pattern's value matcher and a binding-aware syntax parser are related libraries, not interchangeable representations.

The ecosystem illustrates distinct embeddings:

| Language | What changes above the shared core |
|---|---|
| Typed Racket | Expansion-time checking, boundary enforcement and type-directed optimization. |
| Datalog | A reader and syntax front end feeding a logical evaluator. |
| Scribble | Text-oriented reading and document-building libraries; the at-expression reader is in `R:pkgs/at-exp-lib/scribble/reader.rkt:1`. |
| Redex | Grammars, judgments and reduction relations as an executable semantics DSL. |
| Lazy Racket | Delayed application with explicit forcing and strict interoperability. |
| FrTime | Operations lifted over time-varying behaviors and events. |

[Lazy Racket's manual](https://docs.racket-lang.org/lazy/) and Cooper–Krishnamurthi's [*Embedding Dynamic Dataflow in a Call-by-Value Language*, ESOP 2006](https://static.cs.brown.edu/~sk/Publications/Papers/Published/ck-frtime/) show that embedding can change evaluation strategy. These are separately named languages, not evidence that adding an optional analysis may alter Klara's evaluation order. F's forcing-time effects and forkable-thunk constraints still apply.

### Types as macros, and types as predictors

Chang, Knauth and Greenman's [*Type Systems as Macros*, POPL 2017](https://www.cs.umb.edu/~stchang/pubs/ckg-popl2017.pdf) presents Turnstile: typing judgments both check and elaborate syntax, reusing macro binding infrastructure. Rule-oriented definitions support multiple typed embedded languages without changing the host compiler. This is a useful authoring language for Klara's custom analyses, but not automatically a soundness theorem for a new type system.

There is a crucial restriction relative to Turnstile. J requires types not to feed back into ordinary expansion (`K:doc/background/research/J-type-systems-as-predictors.md:169`). Therefore offer two interfaces: **language elaborators** may define distinct semantics, explicitly selected by the programmer; **predictor rules** analyze the resulting K0 and may reject checked claims or license equivalent residuals. A type-directed overload changing which addition executes belongs to an elaborator with a named language identity. It cannot masquerade as removable predictor evidence.

Typed Racket's language front end expands enough syntax to inspect core forms, checks them, generates boundaries and applies type-directed rewrites before ordinary compilation. Occurrence typing refines a variable's type along predicate-controlled paths; mutation and aliasing constrain which refinements remain valid. See the [occurrence-typing guide](https://docs.racket-lang.org/ts-guide/occurrence-typing.html). Its [optimizer](https://docs.racket-lang.org/ts-guide/optimization.html) exploits numeric, list and vector information, including specialized arithmetic and avoiding redundant checks. Klara should attach such facts to canonical K0 paths, preserving macro provenance for diagnostics rather than requiring a typing rule for every macro expansion.

Gradual boundaries are a separate cost center. Takikawa et al.'s [*Is Sound Gradual Typing Dead?*, POPL 2016](https://www2.ccs.neu.edu/racket/pubs/popl16-tfgnvf.pdf) evaluates combinations of typed and untyped modules: intermediate migrations can be much worse than either endpoint. The lesson is to benchmark boundary topology, not just fully typed kernels. Today's [Typed Racket guide](https://docs.racket-lang.org/ts-guide/typed-untyped-interaction.html) distinguishes Deep contracts, Shallow use-site shape checks and Optional unchecked interaction. These offer different guarantees; they are not freely substitutable optimizations. Klara should expose the guarantee and amortize checks only when evidence justifies doing so.

### Contracts, blame and affine boundaries

Findler–Felleisen's [*Contracts for Higher-Order Functions*, ICFP 2002](https://users.cs.northwestern.edu/~robby/pubs/papers/ho-contracts-icfp2002.pdf) makes function contracts monitors: check arguments when called and results when returned, reversing responsibility at negative positions. Checking “is callable” once cannot establish future behavior. Racket represents blame parties and swaps them (`R:racket/collects/racket/contract/private/blame.rkt:99`, `:280`); arrow monitors use the swap (`R:racket/collects/racket/contract/private/arrow-higher-order.rkt:87`).

Klara needs this attribution for checked claims, plus *stateful* monitoring for ownership. RFC 0005 explicitly restores boundary contracts when unchecked callers enter statically checked code (`K:rfc/0005-affine-regions.md:174`). Track the provider, caller, source span, basis and violated obligation. A borrow contract must detect retention or use after scope exit; a predicate at entry is insufficient. Erasing a monitor requires a derivation covering its future uses. Preserve observable blame and failure timing when optimizing monitored programs; moving an effectful check is not justified merely because successful return values agree.

### Redex, Rosette and miniKanren

[PLT Redex](https://docs.racket-lang.org/redex/) offers executable grammars, metafunctions, judgments, reduction relations, exploration and generated testing. It is a model-testing workbench, not a proof kernel. Klara should have native libraries for these operations over inspectable terms, sharing the existing ansatz semantics rather than maintaining another authoritative specification. Generated tests should compare T0, residuals and the model; counterexamples become replayable receipts.

Torlak–Bodik's [*Growing Solver-Aided Languages with Rosette*, Onward! 2013](https://homes.cs.washington.edu/~bodik/ucb/Files/2013/onward13.pdf) and [*A Lightweight Symbolic Virtual Machine for Solver-Aided Host Languages*, PLDI 2014](https://brinckerhoff.org/clements/2214-csc530/Files/tb-rosette-2014.pdf) lift a host language into symbolic execution and constraint generation. A DSL interpreter can thereby support verification and synthesis. Klara wants this as a symbolic value algebra/interpreter with explicit solver effects: specialize away known syntax, retain symbolic inputs, merge supported symbolic branches, then call the solver. Host functions need models or must remain outside the symbolic fragment. Solver timeouts yield unknown; bounded unsatisfiability does not prove an unbounded program. Solver evidence needs a checked proof or a recorded trust boundary before licensing erasure.

Hemann–Friedman's [*microKanren: A Minimal Functional Core for Relational Programming*, Scheme 2013](https://www.schemeworkshop.org/2013/papers/HemannMuKanren2013.pdf) supplies another useful library: substitutions, unification, fresh variables and interleaved search. Specializing a relational interpreter can eliminate fixed goal construction and some unification; it cannot generally eliminate search or guarantee termination. Preserve the selected answer-stream order and fairness. Keep miniKanren, finite Datalog and probabilistic handlers distinct: shared fork/search machinery does not equate their semantics.

### Datalog efficiency and the Chez boundary

Racket's [Datalog manual](https://docs.racket-lang.org/datalog/index.html) describes function-free clauses and tabling. Upstream [`private/compiler.rkt`](https://raw.githubusercontent.com/racket/datalog/master/private/compiler.rkt) translates statements to Datalog syntax; [`stx.rkt`](https://raw.githubusercontent.com/racket/datalog/master/stx.rkt) builds AST objects and calls the evaluator. [`runtime.rkt`](https://raw.githubusercontent.com/racket/datalog/master/runtime.rkt) indexes clauses by predicate/arity, keeps subgoal facts and waiters, and performs renaming, substitution and unification. Thus compiling the surface does not compile away this runtime engine. Termination claims for finite pure Datalog must not be extended automatically to arbitrary external predicates.

This source evidence establishes remaining work, not a measured disadvantage against Datahike. Datahike's implementation explicitly uses Java ArrayLists, HashSets and HashMaps for execution buffers and probes (`D:src/datahike/query/execute.cljc:97`, `:143`, `:197`). Its generic relations already specialize getters by attribute positions and use transient hash construction (`D:src/datahike/query/relation.cljc:58`, `:90`). Crucially, native probe keys normalize equality semantics (`D:src/datahike/query/execute.cljc:146`). A faster hash container giving different joins is not an optimization.

Racket CS separates language machinery from host compilation. Linklets sit below macros, contain imports/exports, and are instantiated against other instances; one module normally has separate linklets for its phases (`R:pkgs/racket-doc/scribblings/reference/linklet.scrbl:10`, `:46`). Schemify converts a linklet to a lambda for Chez or C compilation (`R:racket/src/schemify/README.txt:1`). The reader/expander/module implementation itself is extracted into the runtime (`R:racket/src/expander/README.txt:1`). This supports I's Klara-owned front half and host-owned backend, as does Flatt et al.'s [*Rebuilding Racket on Chez Scheme*, ICFP 2019](https://www-old.cs.utah.edu/plt/publications/icfp19-rddkmstz.pdf).

Retain I's size escape hatch: CS can interpret large outer forms while compiling inner functions (`R:racket/src/cs/README.txt:133`). Linklet imports suggest explicit executable dependencies, but mutable linklet instances are not Klara's immutable bases. Klara must own their versions and guards.

## 3. A. The language lattice as a metaprogramming model

### Objects and scope

Define a language descriptor as immutable EDN containing references to world definitions:

```clojure
{:language/id :rel/finite-v1
 :grammar grammar-id :binding binding-rules-id
 :readers {:sexp reader-id} :expand elaborator-id
 :reference interpreter-id :observations observation-id
 :effects effect-signature-id :laws law-set-id
 :analyses {:shape shape-id :cost cost-id}
 :maps #{translation-id} :tools {:diagnose diagnostic-id}}
```

A reader/skin alone is not a new semantics. An expander dialect defines a translation; an interpreter value defines evaluation; syntax extensions plus a core subset and laws define a useful language only when their binding and observation rules are specified. Optional fields allow a data-only interpreter without textual notation. Laws have provenance and status, not authority conferred by their presence in this map.

Propose `(with-language L form...)` for lexically scoped syntax, plus ordinary `(interpret L program inputs)` for runtime-selected languages. The former resolves L during expansion under the recorded basis. A runtime value cannot retrospectively change already-expanded lexical bindings; it can select a reader/elaborator for a subsequently supplied fragment. Explicit bridges import Klara expressions or values into DSL syntax. Macro-introduced names retain their defining language's bindings. Same spelling in two languages does not imply same binding.

The descriptor's semantic identity includes grammar, binding rules, interpreter and observation contract; changes produce a new version. Predictor evidence and optimization policy versions index caches separately, preserving J's evidence-independent program identity. A purely presentational skin can map to the same canonical program. Source maps remain available even when two skins share its CodeId.

### Maps and their laws

“Lattice” is a productive design picture, but arbitrary programming languages and translations do not form a mathematical lattice. Use a directed multigraph of languages and maps, containing actual partial orders where available. Core restrictions ordered by inclusion can have intersections; compatible abstract domains have precision orders. Two extensions with conflicting application or binding rules need an explicit composition, not an automatic join.

| Map | Obligation |
|---|---|
| Reader/skin → syntax | Preserve intended parsing, binding provenance and source positions. |
| Elaboration L → K0 | Relate L observations to execution of the elaborated program; state admissible contexts and adapters. |
| Compilation K0 → K-IR → host | Simulation covering results, failure, divergence and observable effects under stated assumptions. |
| Interpretation L × input → result | Defines the executable reference meaning, with its chosen handlers. |
| Abstract interpretation L → A | Sound over-approximation under a concretization; equality of results is not its purpose. |
| Specialization (interpreter, fragment) → residual | Residual agrees with interpreting that fragment on remaining inputs. |
| Approximate translation | Declared metric, observation rule, error composition and licence under RFC 0003. |

Full abstraction is stronger than compiler correctness and is not promised: host contexts must not inspect hidden representations or bypass authority checks. Law transport is also conditional. A Datalog set law does not apply to an ordered stream without an adapter and proof. Cost models do not compose like semantic equivalences; fusion changes allocation and traversal costs.

For fixed basis B and assumptions A, the first Futamura obligation is:

```text
I_L(p, d; B)  ==obs==  run(PE(I_L, p; A), d; B)   when valid(A,B,d)
```

Partial application satisfies this equation without removing overhead. A useful partial evaluator must additionally expose known interpreter control and emit dynamic operations. Specializing PE to an interpreter yields a compiler only with adequate self-application support; neither that projection nor the compiler-generator projection is a v1 prerequisite. C's staged generators and I's matcher code generation are practical first implementations.

Narrowing layers preserve successful observations when annotations are erased; declarations may reject programs. Explicit monitor semantics additionally constrain failures and blame. Exact optimization requires the stronger simulation above. A new DSL may have different semantics, but its meaning is fixed once selected: removing its *analysis* cannot change it. Statistical cost predictions choose candidates; they do not establish any of these laws.

### A fragment moving at runtime

```text
query data + language descriptor + pinned basis
               | parse/elaborate (tracked)
               v
        logical fragment ---- abstract interpreters ----> facts / estimates
               | specialize interpreter on fragment         |
               v                                           | choose plan
         residual K0 + dependencies <-----------------------+
               | K1 -> K2 -> host emitter
               v
        guarded executable OR generic interpreter
```

A query arriving during execution becomes static relative to its database and parameter arguments. Its descriptor, rules, schema and available index specifications can become stable assumptions; actual rows remain dynamic. Generated `code` uses `esc` for fragments and `lift` for persistent constants. It must not lift a connection, index cursor or owned authority. `genlet` can share a residual lookup only where scope, effects and evaluation timing permit (`K:doc/guide/05-staging.md:125`, `:208`).

The map receipt records source and target identities, observation relation, translator/checker versions, assumption set, proof/test/trust status, and source-to-residual correspondence. Compose receipts only when the target representation and assumptions of one map satisfy the next. Record negative syntax lookups and analyzer reduction-channel reads, not just successful name resolutions.

Use the existing specialization cache rather than another DSL cache authority. Before entry, validate the calling basis, schema/layout and relevant handler assumptions; otherwise interpret generically. Different forks may share an executable when these dependencies agree. Database-content-dependent constants additionally require a snapshot identity. Mutable external resources require stronger synchronization than immutable-root guards. After effects have occurred, fallback must resume from a valid frame state or a proven replay-safe boundary, never blindly restart.

## 4. B. Ranked ports and deliberate exclusions

Effort estimates are engineering judgments for a focused prototype, excluding production hardening. **P** means the inspected Racket core's MIT-or-Apache-2.0 terms, with notices retained; separately packaged code needs its own licence check.

| Rank | Port/adapt | Effort | Licence and payoff |
|---|---|---|---|
| 1 | Syntax objects, local expansion and definition-context interfaces | 3–6 weeks | P; reliable scoped languages, binding-aware composition and provenance. Extend existing hygiene. |
| 2 | `syntax-parse`-style classes and failure reports | 2–4 weeks for a subset | P; reusable DSL grammars and source-level errors; integrate generated pattern matchers. |
| 3 | Explicit language descriptors and module-language hooks | 2–3 weeks | P concepts; scoped semantics and tracked language dependencies without importing Racket's namespace model. |
| 4 | Contract combinators, blame paths and monitor specialization | 3–6 weeks, affinity additional | P core; enforce higher-order and RFC 0005 boundaries. |
| 5 | Turnstile-style rule notation over J's analysis protocol | 2–4 weeks | Reimplement concepts; verify Turnstile package licence before copying. Makes custom domains approachable. |
| 6 | Small Datalog front end plus staged evaluator | 3–6 weeks; competitive storage longer | Upstream Datalog declares MIT/Apache; supplies the end-to-end test case. |
| 7 | Redex-style generators, judgments and trace explorer | 3–6 weeks for subset | Check Redex files individually; executable language laws and counterexamples. |
| 8 | Symbolic interpreter and miniKanren library | 4–8 weeks / 1–2 weeks | Independent projects: verify licences; verification, synthesis and relational experimentation. |
| 9 | Linklet-inspired executable interface | 1–2 weeks design; backend substantial | P concepts; explicit imports, closure and portable artifacts, following I. |

Do not port Racket's entire expander/module runtime, Typed Racket's full type hierarchy, transparent deep wrappers on every value, or its global mutable instances. Their integration cost and semantics would displace Klara's worlds. Do not port the Datalog runtime unchanged as a performance solution, FrTime's scheduler as fork semantics, or Lazy Racket's evaluation strategy under existing Klara names. Do not duplicate Chez's backend on the JVM.

Licensing correction: `R:LICENSE.txt:1` offers MIT/Apache; `:5` identifies Chez/CS as Apache-2.0; `:9` identifies BC's LGPL components. Additional bundled libraries and packages have separate terms (`:116` onward). This is an inventory distinction, not blanket permission covering every dependency. Port selected permissive files with attribution; avoid pulling BC runtime code into Klara.

## 5. C. Worked finite-Datalog fragment

Choose finite, positive, nonrecursive Datalog first: set-valued relations, no observable tuple order, no external predicates. A rule with all head variables occurring in its body is safe. The example is:

```clojure
;; Proposed surface; illustrative pseudocode, not a runnable transcript.
(with-language finite-datalog
  (rule (grandparent ?x ?z)
        (parent ?x ?y) (parent ?y ?z)))
;; Query grandparent(a, ?z); a and db remain runtime arguments.
(def q {:find ['?z]
        :where [[:parent '?x '?y] [:parent '?y '?z]]})
```

The nonrecursive elaborator unfolds the grandparent rule into q's two atoms, renaming rule-local variables hygienically. The descriptor points to this reference interpreter, where `extend` unifies an atom with a tuple against an existing substitution, returning either a new substitution or failure:

```clojure
(defn solve [atoms db env]
  (if (empty? atoms)
    [env]
    (mapcat
      (fn [tuple]
        (if-let [env2 (extend env (first atoms) tuple)]
          (solve (rest atoms) db env2)
          []))
      (relation db (predicate (first atoms))))))

(defn interpret-query [q db a]
  (set (map (fn [env] (project (:find q) env))
            (solve (:where q) db {'?x a}))))
```

All helpers denote pure finite operations; this is specification pseudocode. Repeated variables compare using the language's equality, not Java object identity. Empty relations produce no answers; repeated derivations collapse into one result. With parent edges `(a,b)`, `(a,c)`, `(b,d)`, `(c,d)`, the answer is `#{[d]}`.

Attach a staging interface to relation access and substitution operations. During specialization, atoms, variable names and tuple arities are known. `extend` becomes a generator mapping variables to code expressions: first occurrence binds a generated local, repeated occurrence emits equality, and a constant emits a comparison. `solve` traverses the static two-atom list while emitting dynamic iteration. With a parent-by-first-column index, planning selects two indexed probes:

```clojure
;; Residual semantic shape; loop helpers must themselves compile/in-line.
(fn [db a]
  (fold-set
    (fn [out y]
      (fold-set (fn [out z] (conj out [z]))
                out (parent-children db y)))
    #{} (parent-children db a)))
```

The proposed generating extension has this staging boundary:

```clojure
(defn stage-query [q schema]
  (let [plan (plan-query q schema)]
    (code (fn [db a]
            (esc (emit-plan plan (code db) {'?x (code a)}))))))
```

Here `plan-query` and `emit-plan` are proposed helpers implementing the planning and static substitution traversal above. The schema contains descriptions, not live index handles. The returned code closes the generated db/a binders; its dependency receipt is carried separately for installation.

In the displayed residual, no atom dispatch, symbolic environment lookup, renaming or generic unification remains. Data traversal and duplicate elimination remain. `(specialize interpret-query q)` alone presently promises only partial application. Connecting generated functions to S8 also requires lowering the iteration helpers and index operations beyond its current supported subset.

The shape domain checks two-column parent tuples, shared-variable compatibility and result shape. An effect domain proves snapshot reads and absence of opaque predicates. An ownership domain licenses a local transient result set, then freezes it; neither its token nor a cursor escapes. Database index updates happen in separate affine transactions with path copying and frozen roots. Region/fiber authority replaces thread identity as the edit-token owner (`K:rfc/0005-affine-regions.md:116`).

The cost interpreter estimates probe cost plus `degree(a) + sum(degree(y))` over children y, retaining skew uncertainty. It can choose an indexed loop, hash join or scan, but estimates cannot justify deleting checks. Schema and index facts guard the selected representation; statistics affect plan quality only unless used for semantic specialization. Pure set semantics licenses join reordering here; aggregates, negation, host effects and ordered output need new obligations.

Recursive Datalog adds a least-fixpoint interpreter, duplicate suppression and a worklist; specialize rule dispatch while leaving data-dependent iteration residual. Semi-naive evaluation requires its own equivalence argument. Performance work then targets unboxed tuple layouts, direct index cursors, allocation elimination and transient buffers. Retain typed, effect-classified host escape hatches for PSS/Java operations while portable Klara equivalents mature. Staging cannot erase their semantics or magically supply a good join algorithm.

## 6. D. Obligations, falsifiers and decisions

All new obligations are **Open**; the source survey is evidence for feasibility, not their discharge.

| Obligation | Concrete falsifier or experiment |
|---|---|
| Language composition preserves binding | Two nested DSLs capture each other's generated variable; changing a transformer in one fork changes the other. |
| Cached expansion equals fresh expansion | Missing negative lookup, phase dependency or schema read produces different canonical K0. |
| Analysis erasure preserves meaning | Removing shape/cost evidence changes an answer, effect trace or selected overload. |
| Residual simulation | Exhaustively enumerate tiny parent graphs and compare reference, staged T0 and compiled answers, including duplicates and heterogeneous keys. |
| Boundary enforcement survives optimization | A callback violates its result contract, or a retained borrow is used after exit, without correct blame. |
| Ownership and deopt are safe | Two forks mutate one transient, or a failed assumption repeats an already performed host effect. |
| Certificates cover actual execution | Correct logical proof accompanies a wrong index-key normalization, stale schema or mismatched residual hash. |
| Specialization is worthwhile | Measure cold compile/check time, warm throughput, allocations, invalidations and code size against hand-written Klara and Datahike equivalents. |

Agree benchmark gates before implementation: for this fragment, initially target warm execution within 2× a hand-written implementation using identical indices and equality; report compilation break-even rather than hiding startup. Exercise skew, empty inputs, schema edits, fork reuse and alternating guarded/generic calls. Separately benchmark contract-boundary configurations. Failure should narrow the supported fragment or improve emission, not weaken its observation contract.

Questions for Christian:

1. Adopt immutable language descriptors plus lexical `with-language`, with runtime selection limited to explicitly supplied fragments?
2. Accept a graph of semantic maps with genuine lattices only for compatible restrictions and analysis domains?
3. Keep Turnstile-like elaborating languages distinct from removable J predictors, even when both use the same rule notation?
4. Start with finite conjunctive Datalog and hand-written generating extensions, then recursion and general interpreter specialization?
5. Make full effect/failure/blame traces part of boundary-map contracts, with deliberately weaker observations only in named pure DSLs?
6. Prioritize syntax objects and generated-code cache installation before a broad language ecosystem, using Datahike's indexed joins as the first performance gate?
