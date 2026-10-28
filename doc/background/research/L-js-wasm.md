# L. JS and Wasm targets without being a frontend hog (research note, 2026-10-28)

Status markers as in B: **Holds** (read in the source or measured here),
**Conj** (an argued conjecture), **Open**. Paths are relative to
`Development/`.

**Sources.**
- `clojurescript` at `cb66c277` (2016-12-22), as in the earlier study
  `lambda-join/studies/dialects-cljs-jank.md` (cited as *cljs-study*). The
  checkout is old: later Closure, `:checked-arrays` and shadow-cljs behaviour
  are not in it.
- `squint` at `f46460f` (2026-06-21). Sizes were measured on the npm release
  `squint-cljs@0.15.212`, bundled with esbuild (`--bundle --minify`, gzip -9),
  in a scratch directory.
- `wasm_of_ocaml` at `52f5ed29` (2025-01; it has since been merged back into
  js_of_ocaml), `schism-wasm` at `7fbb9ce`, `roaring-wasm` at `400554c`,
  `kotlin` at `ef267439e` (2026-07-29).
- Clojurific: the README of `github.com/WhimsicalCode/clojurific`, fetched
  2026-10-28. There is no local checkout, so no line numbers.
- Hoot: wingolog, "CPS in Hoot" (2024-05-27); Spritely, "Scheme in the
  browser: a Hoot of a tale" (Wireworld post) and the Hoot 0.1.0 release
  post; the Hoot README on Codeberg.
- Wasm status: webassembly.org, "Wasm 3.0 completed" (2025-09-17); the
  `WebAssembly/proposals` tracker as of 2026-10-28; v8.dev JSPI posts; MDN
  `script-src`.
- Dart's dart2wasm was not read. Dart is named only as a WasmGC user, from
  the Wasm 3.0 announcement.

## 1. Disagreements first

1. **The first target should be JS, not Wasm.** The question puts JS and Wasm
   side by side. They are not equal for a dynamic Lisp whose selling point is
   live redefinition. JS lets a running page get new code per definition
   (`import()` of a module, or `Function`) and JIT-compile it at once. On Wasm,
   new code means compiling and instantiating a new module, then linking it
   through tables. Hoot, the most serious Lisp on WasmGC, listed "Environments
   and evaluation" among its *missing* features at 0.1.0 and runs its REPL
   from the Guile side. WasmGC wins on numeric kernels and on languages whose
   types are static. Klara's T3 kernels are such code; Klara's dynamic mode is
   not. **Conj**, and testable by the experiment in §5.

2. **Persistent collections are not the main reason cljs bundles are large.**
   The bloat comes from top-level side effects that reference everything.
   `extend-protocol IPrintWithWriter` at `clojurescript/src/main/cljs/cljs/core.cljs:9489`
   attaches a printer to some thirty types in one top-level form. It
   references every one of them, so DCE cannot drop a type the program never
   uses, once anything prints. The `extend-type` forms on `nil`, `js/Date`,
   `number`, `function` and `default` (`core.cljs:1268-1320`) mutate shared
   prototypes, and the `(set! (.-EMPTY …))` statics (`core.cljs:5222-5227`,
   `6349-6387`, `7333-7353`) are top-level assignments too. Clojurific, an
   ES-module cljs fork with bundler tree-shaking, still reaches only 177 KB /
   35 KB gzip for hello world, against Closure advanced's 110 KB / 23 KB. Its
   README names `goog.math.Long`/`Integer` (in every bundle) and `goog.i18n`
   locale data (about 340 KB) as the gaps, not the collections. **Holds** for
   the mechanism. The lesson is that registration (protocol impls, printers,
   readers, hash and equality tables) must be **data the collapser can
   prune**, never prototype mutation run at load time.

3. **Squint's data mapping is wrong for Klara, but squint's emitted code is
   the target to beat.** Squint keeps payloads small by mapping keywords to
   strings and maps to mutable objects (`squint/README.md:62-84`). That breaks
   Klara's value semantics: `=`/hash laws, keys that are collections, and
   structural sharing across forks. But look at what squint emits for
   `(assoc {:a 1} :b [1 2 3])`: `((G__1)=>((G__1["b"] = [1, 2, 3]),G__1))(({"a": 1}))`,
   which is an in-place mutation of a fresh literal (measured, `data.mjs`).
   That is a **uniqueness specialization**, and the KRI already lists
   uniqueness evidence under Memory (`klara/doc/architecture.md` §2). The
   collection representation should be chosen at K2 per value, guarded or
   proved. It is not a fixed choice of dialect. A Klara program whose maps
   provably never escape, never become keys and are never forked can get
   squint-sized output without giving up its semantics. **Conj.**

4. **JSPI is an async bridge, not an effect-handler mechanism.**
   wasm_of_ocaml uses it this way. `suspend_fiber` is wrapped in
   `WebAssembly.Suspending` and resumes through a `Promise`
   (`wasm_of_ocaml/runtime/wasm/runtime.js:112-118, 445-447, 551-552`), so
   every suspension goes through the microtask queue. It is also one-shot, as
   is the stack-switching proposal (Phase 3). Hoot's author describes stack
   switching as one-shot delimited continuations, the feature that would
   remove the need for CPS. Klara's `choose` under exact enumeration resumes a
   continuation more than once (`klara/README.md`, first example). **No
   native Wasm or JS mechanism provides multi-shot continuations.** On every
   web target the M row of note G §3.2 (CPS residual or replay) is the only
   option, and stack switching, once it ships, replaces only T1/T1′. **Holds**
   for one-shot; **Conj** that JSPI's per-perform cost rules it out for
   anything but host I/O. It is unmeasured here.

5. **The KRI table understates the web hosts.** Its Wasm/JS column
   (`architecture.md` §2) says "`WebAssembly.instantiate` / `Function`" for
   code loading and "sci" as the JS T0 seed (§3). Two corrections:
   - CSP splits code loading three ways. Without `'unsafe-eval'`, the page
     cannot use `eval` and `Function`. Wasm compilation needs
     `'wasm-unsafe-eval'` or `'unsafe-eval'`. `import()` of a same-origin URL
     needs only `'self'` (MDN `script-src`; the `import()` case is the
     standard reading of script fetches, not stated on that page). Code
     loading must therefore be a capability with three variants, not one
     operation.
   - sci on JS brings the cljs runtime with it, the very payload this note
     tries to avoid. Klara's T0 seed on JS should be Klara's own K0
     interpreter, emitted by Klara.

6. **Collapse is not Closure's advanced mode, and must not become it.**
   Advanced mode also makes closed-world assumptions: renaming, DCE, and
   static dispatch, which it switches on silently (cljs-study C12,
   `closure.clj:1822-1849`). It never records them, and they change
   observations: keyword identity depends on the optimization level
   (cljs-study C10). Klara's collapse has to be the same specialization with
   the receipt kept. See §4.

## 2. Target matrix

Sizes are measured where a source is given and otherwise budgets (**Conj**).
"Startup" is qualitative, because nothing was timed here.

| | **JS dynamic** (dev, live page) | **JS collapsed** (ship) | **WasmGC** | **Wasm linear memory** |
|---|---|---|---|---|
| Runtime size | client shim ≤ 20 KB gz plus world and collections; T0 and the expander are lazy (§4) | 2–15 KB gz depending on features (§3) | precedent: Kotlin/Wasm hello world 30,922 B wasm + 7,204 B mjs after IR DCE (`kotlin/compiler/testData/codegen/box/size/helloWorld.kt:4-5`); Hoot Wireworld 28 KiB gz | must ship an allocator and a GC or RC. Chrome's WasmGC post: C/Rust fannkuch 6.1–9.6 K against 2.3 K for the Java build, the gap being `malloc`/`free` |
| Startup | dominated by fetching per-definition modules; cached by CodeId | parse and compile of one small ES module | streaming compile; runtime types are declared up front | streaming compile, plus heap initialisation |
| Collections | full CHAMP/RRB (needed for the world and for forks) | per value at K2: persistent, transient-unique, or plain JS array/object under a uniqueness proof | CHAMP nodes as `(array (mut (ref eq)))`, as wasm_of_ocaml's `$block` (`runtime/wasm/effect.wat:39`); fixnums as `i31ref` | RC with in-place reuse (Perceus) is possible; every value crossing to JS is copied or handed over as a handle |
| Effects | tail ops: direct calls. Abort: JS exceptions without stack capture. General one-shot: generators or selective CPS. Multi-shot: CPS or replay | the same, with handlers resolved statically. Most regions become direct code | tail/abort: direct calls and Wasm 3.0 exception handling. General: CPS (wasm_of_ocaml `--enable=effects`, `effect.wat:401ff`, `gc_target.ml:1709-1713`), or JSPI for async only; stack switching later | same as WasmGC, or an explicit shadow stack in the Hoot style |
| Interop | JS objects are Klara host resources at no cost; Klara closures are JS functions | the same; renaming is up to the bundler, so externs are never needed (Clojurific drops them) | WasmGC structs are opaque to JS; access needs exported accessors; JS values are `externref`; strings through JS string builtins (Wasm 3.0) | copying, or manual lifetime: roaring-wasm's buffers are "allocated in WASM memory and not garbage collected" and must be `dispose()`d (`roaring-wasm/packages/roaring-wasm-src/ReadonlyRoaringBitmap32.ts:70-73`), or scoped by `RoaringArenaAllocator` |
| KRI | full: world cells, publication, code load (by URL or `Function`), guards, fibers on the event loop | **KRI-core only**: values, collections in use, control, interop. No world, no code loading | KRI-core in Wasm plus a JS glue module; code loading by module instantiation (heavy) | KRI-core plus memory and authority. A kernel ABI, not a language host |
| Fit | dev and the in-browser REPL | shipping applications | T3 numeric kernels and DSL residuals (wandler, foerster) | existing C kernels (CRoaring), or metacarp output through LLVM wasm32 |

Notes on the matrix:

- **Schism** is the cautionary early case. Before the GC proposal shipped,
  Wasm Scheme allocated through the JS host
  (`schism-wasm/rt/rt.mjs:105-106`: "The allocators and accessors should be
  replaced by the GC proposal") and tagged fixnums in JS numbers
  (`rt.mjs:113-120`). Every cons crossed the boundary. WasmGC removes that
  cost, but schism's 84 KB self-hosted stage-0 compiler
  (`schism-stage0.wasm`) gives a useful order of magnitude for a small
  compiler compiled to Wasm.
- **wasm_of_ocaml** shows the tooling a serious WasmGC back end needs.
  Runtime primitives are hand-written WAT (about 15k lines across
  `runtime/wasm/*.wat`). They are linked and pruned by Binaryen's
  `wasm-merge`, `wasm-metadce` and `wasm-opt`
  (`compiler/lib-wasm/binaryen.ml:50, 102, 125`), with a reachability graph in
  `runtime/wasm/deps.json`. Effects come in two builds: JSPI by default, and
  CPS when the effects flag is on (`generate.ml:1180, 1225`). This split
  matches Klara's grading: pay for CPS only where general operations exist.
- **Kotlin** keeps size budgets as tests. The expected output size is part
  of the test file (`…/box/size/*.kt`), so a size regression fails CI. Klara
  should copy this as it stands (§6).

## 3. Payload discipline

**Principle.** A collapsed artifact pays for a feature only if the
program's latent effect row or its reachable K2 terms mention it. Each
feature below is assigned to an effect or an operation that the level-0a
predictor already computes (`architecture.md` §6), so "is X needed?" is a
static fact and not a guess by the bundler.

| Feature | Absent unless | Pruning mechanism |
|---|---|---|
| Persistent map/vector/set | a value of that kind reaches a non-unique, escaping or forked position | K2 representation choice; runtime split into one ES module per operation (squint's `core.js` exports 252 top-level functions, each separately shakable) |
| Printing, reader | `pr-str`, `read-string`, REPL | printers held in a dispatch table keyed by type, emitted only for types that are both constructed and printed; no `extend-protocol` at top level (§1.2) |
| Equality and hash for all types | `=` on values of unknown type | per-site specialization; the generic `=` table contains only constructed types |
| The world (cells, versions, publication) | a `:world/*` operation (read after start, publish, fork) | collapse declares every cell static; reads become constants; the world module is unreachable |
| Expander, analyzer, T0 | `eval`, `run` on code not known at build time, or `:code/load` | `run` is treated as an operation. When its argument is closed at build time, collapse stages it ahead of time, which is the s-m-n law. Otherwise the manifest must grant `:code/load` explicitly, or the build fails |
| Effect machinery | general or multi-shot operations | tail ops become calls and abort ops become `throw`. The CPS runtime (frames, trampoline) is linked only for general regions, and the replay or multi-shot runtime only for M-class handlers |
| Big numbers | numeric operations not proved within range | Tier M law on JS (§6); BigInt paths are linked only where reachable |
| Fork authority accounting (RFC 0001) | `fork` in the program | absent with the world |

**Budgets** for the collapsed JS artifact, min+gzip, to become CI tests in
the Kotlin style:

| Program | Budget | Precedent |
|---|---|---|
| hello world (`println`) | ≤ 3 KB | squint: 5,005 B min / **1,992 B gz** (measured) |
| data transform, no fork, maps unique (`assoc`, `update`, `mapv`, `reduce`, `pr-str`) | ≤ 6 KB | squint: 8,016 B / **3,010 B gz** (measured, same program) |
| same with escaping persistent maps and vectors | ≤ 15 KB | immutable.js 5.1.9 `Map` alone: 65,534 B / **18,611 B gz** (measured; it does not tree-shake). Clojurific hello: 35 KB gz. Closure advanced hello: 23 KB gz |
| SMC model with `choose`/`observe` under a particle filter handler | ≤ 25 KB | none found; this is Klara's distinctive case |
| WasmGC hello | ≤ 40 KB raw wasm+glue | Kotlin/Wasm 38 KB raw total (above); Hoot "kilobytes, not megabytes" |

The 15 KB line is the claim that matters. A hand-written CHAMP map plus RRB
vector, with `=`, hash and seq, written as separately importable functions,
should fit in about 8–10 KB gzip (**Conj**). If it does not, the budget is
wrong, not the design, and the experiment in §5 will show which.

## 4. Collapse and dynamic mode

### 4.1 Collapse is closed-world specialization with a receipt

Collapse takes a **manifest**: entry points; the cells declared static (by
default all of them); granted capabilities (`:code/load` with its variant
`:url`, `:function` or `:wasm`, plus `:host/*` APIs, `:fork`); the target
and its numeric law. It then runs the ordinary pipeline. Each guard whose
assumption the manifest makes true is **discharged at build time**, and the
discharge is recorded. The vocabulary already exists in S3's certificates
(`klara/doc/guide/06-certified-optimization.md:100`, e.g.
`[:input-is-list-nat :guarded]`). Collapse adds one status, `:baked`, with
the manifest clause that justifies it:

```clojure
{:artifact "app.js" :manifest-hash "…" :target :js/es2022
 :baked [[:cell klara.app/config :static  {:version 17}]
         [:handler :choose :lexical-static {:clause-kind :general :one-shot false}]
         [:repr klara.app/m :js-object    {:evidence :unique-local}]
         [:numeric :js/safe-int-or-throw  {:law "tier-m/js-numbers"}]]
 :absent [:world :expander :t0 :code/load]
 :guarded [[:arg 0 :nat-list]]}
```

Comparison with Closure's advanced mode:

| | Closure advanced | Klara collapse |
|---|---|---|
| Closed-world assumptions | implicit (no `eval`, no reflection, every property statically known) | listed in the manifest; each one is `:baked` in the receipt |
| Renaming | yes; externs needed for foreign code | left to the bundler on ES modules; host access goes through explicit interop forms, so nothing needs externs |
| Static dispatch | switched on silently (`:static-fns`); breaks redefinition | it is the discharge of the cell guards; legal because the manifest says the cells are static |
| Semantics | may change (identity by build mode, cljs-study C10) | must not change: collapsed ≡ T0 on every observation not listed under `:absent` |
| Undo | rebuild | delete the artifact. Tiers are caches (R3); the same source runs dynamically |

Guards that collapse cannot discharge, such as argument shapes from
profiles, stay guards in the emitted code, with a generic fallback compiled
in. That fallback is what keeps the "deleting every cache changes no result"
principle true in shipped code. A collapsed build with no generic fallback
is legal only when every guard is `:baked` or proved.

### 4.2 Dynamic mode in the browser

Three options, which compose:

**(a) Remote compiler (first).** The JVM Klara process holds the expander,
analyzer and emitter. The browser holds a **world mirror**: cell id →
current executable and version, plus the pinned basis of each running
fiber. A REPL form is compiled on the JVM to an ES module named by its
CodeId and served same-origin, and the page loads it with `import()`. This
is squint's vite design: eval over the dev server's WebSocket
(`squint/vite.js:1-20, 98-114`), with the REPL listener stripped from
production builds (`vite.js:252`). Klara changes one detail. Squint
`eval`s strings (`vite.js:114`). Klara loads modules by URL, so the dev page
works under a strict CSP without `'unsafe-eval'`, and code identity is a URL
the browser caches. Publication on the client is a single swap of the
mirror's root, mirroring the JVM's one CAS (`architecture.md` §2), and forks
are a second root. Client cost: world mirror, persistent collections and the
loader, ≤ 20 KB gz on top of the app (**Conj**).

**(b) Lazily loaded T0 plus expander (offline, or an end-user REPL).** The
same Klara sources (`klara/src/klara/{expand,eval,world,defs}.clj`, 1,667
lines today) emitted through the JS back end as a separate module, fetched
on first `eval`. It needs no code loading at all, since T0 interprets, so
it works under any CSP. Budget ≤ 150 KB gz (**Conj**; schism's whole
compiler is 84 KB raw wasm). This is the path for notebooks and for agents
running in the browser.

**(c) In-browser emitter.** (b) plus the K3 JS emitter, loading by
`Function` or blob URLs, which needs the CSP grant. It is only worthwhile
when T0 is too slow in the browser and no server is available. Defer it.

None of the three ships with an application unless the manifest grants
`:code/load` or `:eval`.

## 5. Recommendation

1. **The first web target is collapsed JS as ES modules**, emitted from K2
   (from K0 at first) by a Klara-written K3 JS emitter. The runtime is a
   `klara-rt` package of per-operation modules with no top-level
   registration side effects. It needs no Closure, no externs and no
   bundler-specific plugin; esbuild or Vite does the shaking. This follows
   Clojurific's move (ES modules, `import()` for splitting), minus the cljs
   runtime it inherits.
2. **Dynamic mode, option (a)**: the JVM REPL compiles and the browser loads
   per-definition modules by URL. Option (b) follows once the JS emitter can
   compile Klara's own expander.
3. **WasmGC second, and as a kernel target only.** T3 kernels (fused folds,
   raster/wandler pipelines) are emitted from the same K2 as typed WasmGC or
   plain numeric Wasm and called from the JS host. They share no heap
   objects beyond arrays passed in and out. Revisit a whole-language WasmGC
   host after stack switching ships and only if JS collapsed loses a
   measured benchmark by more than 2×.
4. **Linear memory only for foreign kernels** (CRoaring-style, or metacarp
   through LLVM), wrapped as Klara host resources whose lifetime comes from
   the authority/region discipline instead of `dispose()`.
5. **Effects on JS**: tail ops become calls, abort ops become exceptions,
   general one-shot ops become selective CPS (generators where profitable),
   and multi-shot ops get the CPS residual or replay. JSPI is used only for
   host `:io` that awaits a promise. This is note G §3.2 with JS
   realizations.

**The smallest experiment** (a few days). Hand-write a K0 → ES-module
emitter for the subset in use: `fn`, `let`, `if`, calls, literals,
`perform`/`handle` with tail and abort clauses, and one general clause by
CPS. Collapse three programs: (i) hello world; (ii) §5's
`(reduce + (map inc xs))` with an `assoc`/`update` data step; (iii) the
README's enumerate-both-choices handler, which is multi-shot. For each
program:
- bundle with esbuild and record min and gzip sizes against the §3 budgets
  and against squint (1,992 B and 3,010 B gz, measured);
- check the output against the JVM transcript (the same printed result);
- emit the receipt (`:baked`/`:absent`) and check by grep that the bundle
  contains no world, expander or CPS runtime for (i) and (ii).

Then run (ii) with the map escaping, to measure the cost of the persistent
collections in isolation.

## 6. Obligations and falsifiers

| # | Obligation | Falsifier |
|---|---|---|
| L1 | **Collapse adequacy.** A collapsed artifact agrees with T0 on every observation not listed under `:absent` (R3 extended to artifacts) | a transcript whose collapsed output differs from T0 with all receipts `:baked` truthfully |
| L2 | **No build-mode identity.** `identical?`, keyword equality and hash do not depend on collapse, minification or the bundler (cljs-study C10) | a value whose `identical?` or hash differs between the dynamic and collapsed builds |
| L3 | **Numerics on JS are a declared Tier M law.** Proposed: integers are JS doubles while exact, with exact-or-throw outside ±2^53 (S3's exact-or-throw on longs moved to the JS range) and BigInt behind a guard. Hashes of integers agree with the JVM within the exact range | a program that silently loses precision, or a hash that disagrees with the JVM in range |
| L4 | **Size budgets are tests** (§3 table, in the style of `kotlin/…/box/size`) | the data/persistent program above 15 KB gz with only `assoc`/`get`/`=`/`pr-str` used means the runtime is not pay-as-you-go |
| L5 | **No load-time registration.** No runtime module performs a top-level side effect that references another type | any `klara-rt` module retained by the bundler in hello world that is not on the call graph |
| L6 | **Capabilities, not failures.** A missing `:code/load` or `:eval` is a build error naming the call site, never a runtime surprise | a collapsed build that reaches T0 or the loader without the grant |
| L7 | **Multi-shot on the web** works by CPS or replay, and its cost is confined to M-class regions | CPS frames present in a bundle with no multi-shot handler |
| L8 | **JS before Wasm** (§1.1) | a measured case where WasmGC Klara beats collapsed JS by more than 2× on a non-kernel benchmark (collections, dispatch) with comparable size; then reorder |
| L9 | **Remote-compiler dev under a strict CSP** | the dev page needing `'unsafe-eval'` for the REPL |

## 7. Questions for Christian

1. **Who uses the browser REPL?** Only developers, which makes option (a)
   enough for a year, or end users and agents in shipped pages, which brings
   option (b) forward and needs the 150 KB budget defended?
2. **Numeric law on JS (L3).** Do you accept exact-or-throw at 2^53, or do
   you want BigInt for all integers, which is slower and larger but the same
   law as an arbitrary-precision host? The choice also fixes hash
   compatibility with the JVM.
3. **Multi-shot in the browser.** Is replay (spindel-style) acceptable for
   `choose` under enumeration on the web, or must the CPS residual be the
   only implementation, for one code path on all hosts?
4. **Split the KRI** into KRI-core (values, control, interop) and
   KRI-dynamic (world, code loading, guards, fibers), so that a collapsed
   host implements only the first? It changes `architecture.md` §2.
5. **Strict CSP as a design constraint.** Should "no `'unsafe-eval'`, ever"
   hold in dev as well as in shipping builds? It forces loading by URL and
   rules out option (c).
6. **Is WasmGC as a kernel target only** acceptable, or is a full WasmGC
   host a goal in itself, for instance for edge runtimes without a JS JIT?
