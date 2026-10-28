# D. Dispatch, polymorphism, à-la-carte typing, hosting and Clojure interop

Research note, Klara iteration 0, 2026-10-27. Builds on algebras.md §1, narrowing.md, design-decisions.md (D7, D10, D13, D14), studies/*, v0, raster and clojure-conformance. Nothing here modifies code.

## 0. Disagreements first

1. **"Zero-overhead bidirectional interop" holds for values and calls, not for definitions.** A Klara map can pass through `clojure.core` at near-native speed, and Klara can call a Clojure `IFn` with one `invokeinterface`. But linked Clojure code reads var roots on every call, uses thread-local `binding` frames, and dispatches protocols with last-loaded-wins. None of that can respect a fiber's pinned basis (algebras.md:68-71, law D-4), and none of it is forkable. Linked mode is therefore Tier H by construction, and the design should say so instead of promising more. Only hosted mode is inside the guarantees.
2. **raster conflates two things that Klara must separate.** In `deftm`, a parameter type is at once a *dispatch pattern* and a *representation license* (raster/design/type-system.md:45-66). Adding a `Float` method to `norm` changes the result for float arguments, because float arithmetic differs from double arithmetic. That is legitimate, since a new method is a new *definition*. But the design principle (00-design-space.md:44-47) says annotations "never change meaning". So the type in a method's dispatch pattern must be syntactically distinct from a type annotation on a binding. The first may change meaning. The second may only reject programs or license representations. Without this split, the gradual guarantee is false on the shaped rung from day one.
3. **Julia-style multiple dispatch over host classes buys little for Clojure-style data code.** Idiomatic Clojure values are overwhelmingly `PersistentHashMap`/`PersistentVector`/`Keyword`, so a class tuple barely discriminates. The real polymorphism lives in *values*: a `:type` key, a key set, a sealed variant. Multiple dispatch earns its keep on numerics and kernels (raster's domain). The default fragment should therefore be single dispatch plus declared value-keyed dispatch, with multiple dispatch as an opt-in fragment. This refines algebras.md:78-93 instead of overturning it.
4. **Law D-3 (collision = conflict) as implemented in v0 fights the REPL.** Re-extending your own op at the REPL is the normal loop, yet v0 demands `:force` (v0/src/v0/dispatch.clj:169-173). An extension needs an *owner* so that a redefinition by the same owner is a new version and a competing owner produces a conflict.

## 1. What prior docs and code already settled

- **The dispatch algebra.** `resolve : (op, key(args), world) → impl | ⊥ambiguous | ⊥none` (algebras.md:27-41). Law D-1 makes the unique most-specific candidate win, and makes incomparability an error (:45-53). D-2 makes adds that could not change a resolution invalidate nothing (:54-59). D-3 is coherence by collision (:60-67). D-4 puts extension tables under var visibility (:68-71). D-5 is the progress-or-saturate IC lattice (:72-76). The instance lattice runs single → multiple → value → predicate → host-virtual, and *the op declares its fragment* (:78-93). The realization ladder runs direct call → PIC → table → world-indexed (:95-124). Falsifier: PIC-realized predicate dispatch must come within ~2x of protocol dispatch on monomorphic sites (:167-169). The redex probe measured a coarse "table changed" protector over-firing on 92.5% of sites (:158-163).
- **v0.** `v0/src/v0/dispatch.clj:50-67` implements `resolve` over an `isa?` product order. It has a per-op memo cache with a coarse protector and an optional winner-hash firewall (:90-111), D-3 collisions with hash-idempotence (:154-179), and fragments `:single`/`:multiple` keyed on `class` (:73-81). It has a single world, so D-4 is only partial (:12-13). `v0/src/v0/shape.clj:33-102` has sealed shapes with expansion-time exhaustiveness. `v0/src/v0/bridge/raster.clj:29-43` crosses into a raster kernel by stamping `^{:- T}` metadata, falling back to `Object` as a visible slow path, never a wrong result.
- **The narrowing ladder.** general → shaped (raster, L1.5) → affine (Carpaccio, L1) → proved (ansatz, L0). The seam is "metadata + EDN, not a registry" (narrowing.md:14-40).
- **Typing stance (D10).** Four Typed Clojure commitments: checker-as-library, macros carry rules, per-def content-hash keys, and blame contracts insertable by the checker (design-decisions.md:456-494). Six Elixir rules, among them infer-never-require, provable-errors-only and performance-as-contract (:495-520, studies/elixir-types.md:93-106).
- **Redefinition (D14).** Copy Julia's world-age semantics, but drop the single scalar epoch, the eager invalidation storms and the late retrofit (design-decisions.md:722-760). Steal Truffle's Assumption/CyclicAssumption and its bounded reoptimization budget (:761-778). V8 analysis: the var cell is already the choke point, so every var can be a protector cell with no added write barrier (studies/v8.md:77-85).
- **Interop/hosting (D13).** Hand-specialize persistent cores, use call-site/link-time specialization, and never an AOT specializer (design-decisions.md:698-717, studies/scala.md:75-86). Kotlin: contracts per declaration, `actual typealias` ("alias, don't wrap"), and design the escape hatches in up front (studies/kotlin.md:213-246). Roc: adopt requires/provides and the RocOps table; reject exclusivity, so a platform is a handler stack (studies/roc.md:251-295). Truffle is not the primary JVM strategy, because a persistent DS gets no interop message for functional update (studies/graal-truffle.md:79-92). SCI's `fork` leaks re-defs, multimethods and `derive` (studies/dialects-wasm-basilisp-sci.md:109-115).
- **Hash/equality are Tier L and non-negotiable** (design-decisions.md:360-386). Tier partition: `=`/`hasheq` and protocols/multimethods are Tier M; `deftype`/`reify`/`proxy` are Tier H; direct linking is an open item (clojure-conformance/doc/tier-partition.md:54-55, 69-73, 93-96).
- **raster** shows typed multiple dispatch on the JVM. It runs a boxed fallback plus `.invk` on a generated primitive interface (~20 ns generic vs ~0 walked, type-system.md:174-186), and its call sites are `MutableCallSite`s invalidated on redefinition (raster/src/raster/runtime/callsites.clj:1-10; core.clj:387-416).

## 2. External survey (verified)

- **Julia.** Bezanson et al., "Julia: dynamism and performance reconciled by design", OOPSLA 2018, https://doi.org/10.1145/3276490. Performance comes from specializing on concrete argument types and devirtualizing inside type-stable code. Pelenitsyn et al. formalize *type stability*, "the concrete output type is determined by the concrete input types", as the precondition (OOPSLA 2021, https://arxiv.org/abs/2109.01950). The cost side is invalidation: Holy, Bezanson and Nash report Makie at 3273 → 129 invalidations after targeted fixes (https://julialang.org/blog/2020/08/invalidations/), and the problem recurred in 1.11/1.12 (https://julialang.org/blog/2025/05/this-month-in-julia-world/). Lesson: multiple dispatch is fast *because of* whole-call-graph specialization, and you pay for that in redefinition latency.
- **Clojure.** Protocols generate an interface, and direct implementation is the fastest path. `extend` covers types you don't own, and the stated aim is the expression problem (https://clojure.org/reference/protocols). Mechanism, observed in the Clojure jar we depend on: compiled protocol call sites get a per-site class cache (`__cached_class__N` fields, Compiler.java:5801-5805), which is a monomorphic inline cache, plus a per-fn `MethodImplCache`. `MultiFn` caches by dispatch value and flushes when the hierarchy changes (MultiFn.java:26-27). Keyword lookups on records use `KeywordLookupSite` inline caches. Var roots notify watches on `bindRoot`/`alterRoot` (Var.java:278-315). That hook is the basis of the linked-mode protector in §4.
- **Polyglot interop.** Grimmer et al., "High-performance cross-language interoperability in a multi-language runtime", DLS 2015 (https://2015.splashcon.org/details/dls2015/15/High-Performance-Cross-Language-Interoperability-in-a-Multi-Language-Runtime), and TOPLAS 40(2) 2018. Language-independent messages are resolved into foreign-specific operations at first execution: no marshalling, and the compiler optimizes across the boundary. Our study's caveat: there is no message for persistent update, so immutable host collections end up claiming to be mutable (studies/graal-truffle.md:41).
- **Roc platforms.** Every application runs on exactly one platform, the core has no I/O, and the platform API is an ordinary Roc API. Source: the Roc README, https://github.com/roc-lang/roc. The wording above is from 2020–21 snapshots; the current mechanics, read at HEAD 0c819911, are in studies/roc.md:45-125.
- **Kotlin/Java interop.** Java types become *platform types* `T!` with relaxed null checks, and annotations (JSpecify, strict by default) upgrade them into real types (https://kotlinlang.org/docs/java-interop.html). It succeeded by admitting unsoundness at the boundary and making it cheaper to annotate than to wrap. **Scala/Java collections:** conversions are wrappers, "collections are never copied", and immutable Scala collections throw `UnsupportedOperationException` on Java mutation (https://docs.scala-lang.org/overviews/collections-2.13/conversions-between-java-and-scala-collections.html). What failed: converting by hand at every call, and the ABI breaks caused by the JDK adding default methods (studies/scala.md).
- **Gradual typing.**
  - Siek, Vitousek, Cimini and Boyland, "Refined criteria for gradual typing", SNAPL 2015 (https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SNAPL.2015.274). The *gradual guarantee* says that making annotations less precise preserves typability (static part) and preserves the result (dynamic part). A more precise program may only fail more, with a cast error.
  - Takikawa et al., "Is sound gradual typing dead?", POPL 2016 (https://doi.org/10.1145/2837614.2837630). Measured across all typed/untyped configurations of Typed Racket benchmarks, overheads reach >100x, with "valleys" where developers get stuck.
  - Bauman et al., "Sound gradual typing: only mostly dead", OOPSLA 2017. A tracing JIT (Pycket) removes >90% of the overhead on typical benchmarks.
  - Greenman and Felleisen, "A spectrum of type soundness and performance", ICFP 2018 (https://doi.org/10.1145/3234594). Higher-order (natural), first-order (shallow) and erasure semantics trade guarantees for cost.
  - TypeScript deliberately accepts unsoundness, such as bivariant function and array subtyping (Bierman, Abadi and Torgersen, ECOOP 2014, LNCS 8586:257-281).
  - Typed Clojure: Bonnaire-Sergeant, Davies and Tobin-Hochstadt, "Practical optional types for Clojure", ESOP 2016 (https://arxiv.org/abs/1812.03571), with lessons in studies/typedclojure.md.
  - Elixir: Castagna, Duboc and Valim, "The design principles of the Elixir type system", ‹Programming› 8(2) 2024 (https://arxiv.org/abs/2306.06391). Set-theoretic types with `dynamic()`, strong arrows, and no inserted runtime casts.
- **Inline caches.** Hölzle, Chambers and Ungar, "Optimizing dynamically-typed object-oriented languages with polymorphic inline caches", ECOOP 1991, LNCS 512:21-38 (https://bibliography.selflanguage.org/pics.html). V8's IC lattice with an explicit anti-flap law and protector cells (studies/v8.md:77-95).

## 3. Options with trade-offs

### 3.1 Core polymorphism mechanism

| Option | Strength | Cost |
|---|---|---|
| (a) Open multiple dispatch over classes (Julia/raster) | symmetric, solves binary methods and numeric promotion | needs type-stable specialization to be fast; invalidation storms; little discrimination on data code |
| (b) Protocols (single dispatch on class) | maps 1:1 to `invokeinterface`; Clojure parity; cheapest IC | no binary methods; open extension is last-wins |
| (c) Type classes (dictionary passing, coherence) | static resolution, laws per instance | needs static types everywhere, which contradicts à-la-carte; orphan rules are anti-modular (studies/rust.md) |
| (d) One algebra, declared fragments (algebras.md) | each fragment has its natural realization; predicate dispatch as a ceiling | must keep D-laws across fragments; resolution semantics must be identical whatever the realization |

(d) is already chosen, and I agree. The open questions are the *default* fragment and how *shapes* enter. Shape dispatch has two variants. **Nominal shapes** (a sealed variant or record carries a tag; v0.shape) cost one field load to key, and an IC handles them. **Structural shapes** (dispatch on which keys a map has) cost O(keys) per call unless maps carry hidden-class-like layout descriptors, and that changes the map representation for everyone (cf. Truffle's `DynamicObject` shape-obsolescence costs, studies/graal-truffle.md:39). Structural shapes belong in the *checker* (Elixir-style inference) and in *specialization guards*, not in dispatch semantics.

### 3.2 Specialization and REPL redefinition

- **Per-call var deref (Clojure)**: always fresh. The JIT relies on C2 inlining through `Var.getRawRoot`, and HotSpot cannot fold a mutable root.
- **Direct linking (Clojure/jank/cljs)**: fast, but blind to redefinition, so it is a collapse mode (design-decisions.md:827-834).
- **Invalidatable call sites (raster, Truffle)**: a `MutableCallSite` or `SwitchPoint` per var or op, `setTarget` + `syncAll` on redefinition. Cost lands on the writer, readers are free (V8's trade).
- **World-pinned dispatch (Julia, algebras D-4)**: MVCC over extension tables. Old fibers keep old code, raise points re-read heads.

These compose. Semantics is world-pinned; the realization uses invalidatable sites guarded by per-op protectors, refined by the winner-hash firewall. Direct linking is only a named collapse mode.

### 3.3 Typing stance

- **Hints (erasure / speculative)**: a guard plus deopt to the general path. Meaning is preserved *by construction*, there is no blame, and cost is near zero after warmup. No guarantee for the programmer.
- **Shallow contracts (first-order / transient-like)**: check constructors and shapes at boundaries. Cheap on immutable data, and Klara has a trick Racket lacks: a validated persistent value stays valid, so verdicts can be memoized by identity (or content hash). Functions and lazy seqs still escape.
- **Deep contracts (natural / higher-order)**: wrap functions and lazy structures, with full blame. This is the configuration that measured >100x (Takikawa) and needs a tracing JIT to recover (Bauman).
- **Static only (Elixir, TypeScript)**: no runtime cost, and provable errors only. Unsound at the boundary, honestly so.

## 4. Recommendation for Klara v1

### 4.1 Dispatch semantics

1. **One construct, `defop`, with a declared fragment.** The default is `:single`, keyed on the host class of arg₀, which is protocol-shaped and realized as `invokeinterface` when the impl is a Klara type. `:value` takes a declared pure key-fn (a multimethod with D-1 ambiguity errors instead of `prefer-method`-by-default). `:multiple` is opt-in, for numerics and kernels, with raster as its realization. `:predicate` is gated behind the ~2x falsifier.
2. **Shapes enter nominally.** `defshape`/records carry a tag, and dispatch on it is `:value` with a field-load key-fn. Structural shape facts are checker and guard evidence only.
3. **Extensions have an owner** (the defining module's identity). The same owner re-extending creates a new version in the var-history lattice, which needs no `:force`. A different owner at the same `(op, pattern)` is a D-3 conflict surfaced at load or merge time. Clojure-originated extensions (via `extend-protocol` on Clojure protocols) are outside D-3 and are documented as Tier H.
4. **Realization.** Each op has a protector (a `SwitchPoint`, invalidated after publishing the new table, the CyclicAssumption order). Each site is a `MutableCallSite` running the D-5 lattice (mono → poly≤4 → mega → table). Each site keeps its winner hash, so a table change that leaves the winner unchanged does not deopt it (the 92.5% finding). Deopt cycles are bounded by Truffle's numbers (15/100).
5. **Missing-method assumptions are tracked** (Julia's missing-signature edges). A site specialized on "no extension for K" registers on the op's key-class edge.

### 4.2 Typing stance

**Both, syntactically distinct, with hints as the default.**

- **Dispatch patterns** (`(defop area [^Circle c] …)` extensions) are *definitions*. They may change meaning and live under D-1..D-4.
- **Annotations** (`^{:- T}` on locals, params of single-method fns, returns) are *claims*. A claim has three possible grades:
  - *hint* (the default): guard + deopt, never an error, recorded as L2/L1.5 evidence;
  - *checked*: a shallow boundary check at def entry, with blame naming the annotated def, and a memoized verdict for persistent values;
  - *proved*: an L0 certificate that removes the guard.
- Higher-order wrapping is opt-in per boundary, never the default.
- The static checker follows Elixir's rules: infer, never require; provable errors only; one finding per def.

This makes the gradual guarantee provable per rung (§5, O1–O4). It also puts the "sound gradual typing is dead" cost only where someone asked for deep checks.

### 4.3 Interop interface list (JVM, ordered)

The phase-0 decision (00-design-space.md:39-43) uses Clojure's own collections, so parity is automatic until Klara ships its own representations (aspect B). When it does, implement in this order:

1. **Every Klara value:** `IHashEq`, `equals`/`hashCode` per the java.util contracts, `IMeta`/`IObj` (metadata outside equality and hash), `IFn` where callable, and `toString`.
2. **Maps:** `IPersistentMap` (and through it `Associative`, `ILookup`, `IPersistentCollection`, `Counted`, `Seqable`, `Iterable`), **`MapEquivalence`**, **`java.util.Map`** (read-only, mutators throw `UnsupportedOperationException`), `IKVReduce`, `IReduceInit`, `IMapIterable`, `IFn` (lookup). Then `IEditableCollection` + `ITransientMap`.
   - Concrete trap: `APersistentMap.equiv` returns false for any `IPersistentMap` that is not `MapEquivalence`, and requires `java.util.Map` (APersistentMap.java:76-80). Leave out either interface and `(= clj-map klara-map)` is false while `(= klara-map clj-map)` may be true, which breaks symmetry.
3. **Vectors:** `IPersistentVector`, `Indexed`, `IReduce`, `java.util.List`, `RandomAccess`, `Comparable`, `IFn`. Seqs over them implement `IChunkedSeq`, because `reduce`/`doseq` behaviour and chunked effect timing are observable (tier-partition.md:51).
4. **Seqs/lazy:** `ISeq`, `Sequential`, `IPending`, `java.util.List`.
5. **Records/types:** `ILookup` (keyword sites fall back to `valAt`), `IKeywordLookup` later, `IType`/`IRecord` only if Klara records should satisfy `record?`.
6. **Hash parity without copying:** call the public `clojure.core/hash-ordered-coll`, `hash-unordered-coll` and `mix-collection-hash` (the algorithms are specified at https://clojure.org/reference/data_structures). On non-JVM hosts, Murmur3 is public domain and Clojure's `Murmur3.java` itself is Apache-2.0 Guava-derived (its header), so a clean port is licence-compatible.

**Klara → Clojure.** A Clojure fn is an `IFn`, called by `invokeinterface IFn.invoke` at its arity. Non-dynamic Clojure vars are cached in a `MutableCallSite` invalidated by an `add-watch` on the var (roots notify watches, Var.java:278-315). That gives a protector over Clojure vars with no Clojure fork. Dynamic vars are always dereferenced per call. Clojure protocols are called through their `IFn`.

**Clojure → Klara.** Klara types are **real emitted JVM classes** (hidden classes where unloading matters), so `extend-protocol` works and protocol call-site caches hit. SCI's single wrapper class is the counterexample (studies/dialects-wasm-basilisp-sci.md:121-124). Klara ops implement `IFn`, and `extend-op!` is callable from Clojure.

### 4.4 Loading modes and what breaks

| Concern | Linked (plain `require`) | Hosted (through Klara's expander) |
|---|---|---|
| defs | Clojure `Var`s, global, last-wins | Klara world entries, basis-pinned, forkable |
| redefinition seen by Klara | via var watches → call-site invalidation | native D-4 |
| dynamic `binding` | Clojure thread-local frames. On Klara fork, capture `Var.cloneThreadBindingFrame` and install it in the child (Var.java:96-104), like `binding-conveyor-fn` | mapped to Klara's dynamic-scope handler; Clojure frames reconstructed at linked calls |
| laziness | `LazySeq` is a locked memo thunk. Across a fork it is a **resource**, not a value: realizing it in one fork runs its effects once for all forks | same object, but the expander can mark producers pure (beichte) and only then classify the seq as a value |
| chunking | observable effect timing (32) | same; Tier M law |
| metadata | outside `=`/hash; Klara provenance must not ride in `meta` if it should affect content hashes | same |
| protocols on Klara types | work (real classes), last-wins, outside D-3 | Klara `defop` with D-3 |
| macros | Clojure's | Klara's compat expander (v0/src/v0/compat.clj), with host passthrough measured |
| direct-linked code (all of `clojure.core`) | ignores redefinition | **clojure.core is always linked**, never hosted |

### 4.5 Copyright flags (constraint 4)

- **Fine:** implementing `clojure.lang` interfaces, calling the public hash fns, matching behaviour from documentation and black-box tests, reading third-party library source *at runtime* in hosted mode.
- **Needs care:**
  - **Hosting `clojure.core` itself** would compile EPL source through Klara. Distributing the resulting artifacts (collapse/AOT) creates an EPL derivative inside an Apache distribution. Keep `clojure.core` linked, which is also what direct linking forces.
  - **Constructing Clojure protocol maps by hand**, so that Klara ops *are* Clojure protocols, depends on undocumented internals of `core_deftype.clj`. That invites reading Clojure source and is unstable, so reject it.
  - **`v0.compat`** re-implements core macros and calls `clojure.core/destructure` (compat.clj:15-17). The call is fine, but the clean-room replacement must be written from documentation and tests by someone without the source.
  - **Docstrings:** show them at runtime from the jar, but never bake them into Klara docs.

### 4.6 Hosting beyond Clojure

Treat a host as a **platform value**: a handler stack plus an ops table (the RocOps shape: allocation, panic, diagnostics, hosted fns). Klara's `requires`/`provides` contract is checked at load time. "Total inversion" (Roc) is the configuration in which the host closes the handler stack.

- **JVM apps** embed Klara as a library and see `IFn`s and `java.util` views. This is the Kotlin route: annotate, don't wrap.
- **JS** gets the same contract with a different Tier H. The value contract must not leak JVM `equals` (cljs's baked hashes are a warning, design-decisions.md:382-386).
- **Databases (datahike):** state crosses only as persistent snapshots. A db value is a Klara value; a connection is a resource.

## 5. Obligations and falsifiers

- **O1 (Holds by construction, if 4.2 is implemented): hint annotations preserve meaning.** A guard failure deopts to the general path, so removing a hint changes nothing. Falsifier: a hint whose representation changes `=`/hash, e.g. unboxing a `Long` to `double`, which makes `(= 1 1.0)` true under `==`. Representation licensing must stay inside a value's equality class.
- **O2 (Conj): checked annotations satisfy the gradual guarantee** (SNAPL'15 dynamic part). A less precise program yields the same value; a more precise one may only add blame errors. Proof obligation in ansatz over a core with casts. Falsifier: any check with a side effect, such as forcing a lazy seq to check its elements. Lazy and higher-order values must therefore be checked only by wrapping, or not checked at all.
- **O3 (Conj): affine and proved rungs are pure restrictions.** Erasing them yields a program that copies instead of mutating, with equal results. Falsifier: an affine-licensed in-place update observable through an alias the borrow checker missed (narrowing.md:72-77 lists known conservatisms).
- **O4 (Open): memoized shallow checks on persistent values amortize to under 5% on Takikawa-style configuration lattices.** Falsifier: the overhead on a port of 3 GTP benchmarks exceeds 2x in any configuration.
- **O5 (Conj): symmetric `=` and hasheq parity for Klara collections against Clojure collections.** Falsifier: any property-test counterexample (§6).
- **O6 (Open): a `:single` `defop` realized via `MutableCallSite` + IC comes within 1.2x of a Clojure protocol call on mono, poly-3 and mega sites.**
- **O7 (Holds, measured in model): winner-hash firewall precision** (algebras.md:158-163). Still Open on real workloads; dispatch.clj `:firewall?` exists for exactly this.
- **O8 (Open): REPL redefinition latency.** Re-extending an op used by 10k sites stays below 50 ms wall-clock including deopts. Falsifier: invalidation storm behaviour à la Julia 1.5.
- **O9 (Conj): linked-mode var caching via watches is sound.** Falsifier: a var mutation path that bypasses watches (`Var.setRawRoot`-style internals, or `with-redefs` under concurrent readers) observed in the conformance corpus.
- **O10 (Open): Roc's falsifier carried over.** A handler-mediated hosted call comes within 2x of a direct extern call (studies/roc.md:290-295).

## 6. Smallest experiment

**`KMap`: a Klara map through `clojure.core`, in plain Clojure, no emitter.**

1. `deftype KMap [^clojure.lang.IPersistentMap m _meta]` delegating to a `PersistentHashMap`, implementing exactly the §4.3 map list. Step 2 swaps the delegate for a clean-room CHAMP written from Steindorfer and Vinju (OOPSLA 2015) without looking at Clojure's source.
2. Property tests (test.check, 10k cases over nested maps with mixed numerics, `nil`, keywords, records):
   - `(= km m)` and `(= m km)`;
   - `(= (hash km) (hash m))`;
   - `(contains? #{m} km)` and `(get {m 1} km)`;
   - the `.equals`/`.hashCode` java.util contract;
   - `pr-str` equality;
   - destructuring;
   - `merge`, `select-keys`, `update-in`, `frequencies`, `into`, `reduce-kv`, `keys`/`vals`, `transient`.
3. Criterium benchmark, KMap vs PHM, n ∈ {8, 1k, 100k}: `get`, `assoc`, `reduce-kv`, `into {}`, `=`, `hash`, `(:k m)`, and a `clojure.walk/postwalk` over a 10k-node tree. Write results to a tmp file.
4. Add one `defop :single` over KMap and PHM, invoked from Clojure code compiled normally. Compare against a Clojure protocol on the same two types (O6).

**Pass:** zero property failures; delegate ≤1.1x and CHAMP ≤1.3x PHM on every op; `defop` ≤1.2x protocol. **Fail and learn:** any `=` asymmetry, which would mean an interface is missing or wrong; a hash mismatch on numerics, which would mean D7 parity is harder than assumed.

## 7. Questions for Christian

1. **Two kinds of types?** Should a type in a method's *dispatch pattern* (a new definition that may change results, like raster's `Float` overload) be written differently from a type *annotation* (a claim that may only reject or speed up)? If they share syntax, as in `deftm`, the "annotations never change meaning" principle cannot hold. Splitting them means raster's surface needs an adapter.
2. **What does a wrong annotation do by default?** As a *hint*, a wrong type silently falls back to the slow path, so it is always safe and never an error. As a *contract*, it raises an error that blames the annotated def. I recommend hints by default and contracts per module opt-in. Do you want the opposite for the PL-research audience?
3. **Are you comfortable declaring linked Clojure code outside the fork and basis guarantees?** In practice, a forked world that calls a linked Clojure library sees that library's global state (vars, atoms, half-realized lazy seqs) shared with every other fork. Hosted mode fixes this for libraries, but never for `clojure.core`, which is direct-linked and EPL.
4. **Who owns an extension?** For the REPL to allow re-extending your own op while still catching competing extensions from two libraries, every extension needs an owner identity. Is the module/namespace enough, or should it be a signing key, as in replikativ?
5. **Structural shapes in dispatch: no?** I recommend dispatching only on nominal tags and using key-set shapes for checking and specialization guards. Is there a probabilistic-programming use case, such as dispatching on a trace's address structure, that needs structural dispatch semantics?
