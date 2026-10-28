# I — Chez Scheme as the baseline compiler, pattern as the pass framework (research note, 2026-10-27)

Status markers as in B: **Holds**, **Conj**, **Open**. Paths are relative to
`Development/`.

**Sources.**
- Chez: `ChezScheme` at `origin/main` = `7fadeee4` (2026-08-18), read with
  `git archive` into a scratch directory; the working tree was not touched.
  **The local checkout is stale.** `master` is `cd71c2af` (cisco, Nov 2020)
  and has no `pb.ss`, `arm64.ss`, `cpprim.ss` or `cptypes.ss`. Every
  `s/…:line` and `c/…:line` below refers to `7fadeee4`.
- Racket CS: `racket` at `9fa53a48ad`.
- pattern: `pattern` at `89da31a`, branch `codex/recursive-dialect-sequence-abbr`.
- Papers read: Keep's dissertation (*A Nanopass Framework for Commercial
  Compiler Development*, Indiana 2012, the long form of Keep & Dybvig ICFP
  2013), from Zotero; Flatt et al., *Rebuilding Racket on Chez Scheme
  (Experience Report)*, ICFP 2019, doi 10.1145/3341642.
- Not read here, marked *(recalled)* where used: Waddell & Dybvig SAS 1997;
  Hieb, Dybvig & Bruggeman PLDI 1990; Bruggeman, Waddell & Dybvig PLDI 1996;
  Sarkar, Waddell & Dybvig ICFP 2004.

## 1. Disagreements first

1. **"Chez needs no interpreter tier" is false three times over.**
   - Petite Chez *is* an interpreter. It runs the same front end
     (`s/interpret.ss:672-681`) and installs itself as `current-eval`
     (`s/interpret.ss:732`). Only the full system sets `(current-eval compile)`
     (`s/cback.ss:17`).
   - `compile` itself skips code generation for trivial forms: `cheat?`/
     `cheat-eval` (`s/compile.ss:44-64`, used at `:1820-1823`).
   - Racket CS, Chez's largest client, interprets the outer layer of any
     linklet over 10,000 terms and compiles only the inner lambdas
     (`racket/src/cs/linklet.sls:141-147, 682, 725-760`; paper footnote 2).
     Its compile-from-source time is 55.6 s against 31.8 s for Racket BC
     (1.75×), and the distribution build takes 119 against 62 minutes.

   Chez's lesson is not "no interpreter". It is that **the baseline is a real
   compiler and the interpreter is a size escape hatch.** Klara needs both,
   with a size cutoff.

2. **The nanopass compiler is not the fast one.** Keep's own numbers: the
   nanopass rewrite compiles 1.64–1.75× slower than the compiler it replaced,
   and its back end about 2× slower. It has 10× as many back-end passes, ~50
   passes and ~35 languages in all (dissertation §3.3, §3.6). It generates
   code 15–26.6% faster. About **68% of each pass's time is plain traversal
   and rebuilding** (dummy-pass method, §3.6.2.1). Nanopass buys
   maintainability and code quality with compile time. A Klara pipeline
   written over persistent data pays that 68% at a higher constant.

3. **Chez does no speculation, deoptimization, OSR or invalidation.** It
   inlines across definitions only where bindings are immutable: library
   exports store an inlinable residual in a per-machine box
   (`cte-optimization-loc`, `s/cp0.ss:5801-5847`). Top-level REPL definitions
   are reached through symbol value slots. That is the right T1 model for
   Klara, var indirection with no cross-cell inlining. But the speed people
   quote for Chez is library-compiled code with cross-library inlining.
   Klara-T1 on Chez gets interaction-environment speed, and the gap between
   the two is unmeasured (I-O2).

4. **"Perhaps beyond native" does not transfer.** On the JVM and in JS the
   host JIT *is* the optimizing back end. Bytecode emission is already the
   cheap baseline compiler, and a Chez-style register allocator there is
   wasted work. Chez's design applies to hosts where Klara owns machine code:
   native, and Wasm in its linear-memory form.

5. **On a segmented-stack host, op classes stop deciding compilation
   strategy.** v2 §4 classifies ops as tail/abort/general *at definition
   time*, because the JVM must decide CPS when the performing code is
   compiled. On Chez, general one-shot and multi-shot capture need no code
   transformation (§3). The classification remains useful as a dispatch fast
   path everywhere, but its semantic weight is a JVM/JS artefact. The spec
   should state it as portable semantics with a host-dependent cost model.

6. **pattern today is 25–33× too slow for hot baseline passes** (§5, measured).
   It is the right tool for dialect definitions, validation and rule sets,
   not yet for a compiler that must hit R2 (≤ 5 ms per definition).

## 2. Chez's compiler, verified

### 2.1 Pass pipeline and IRs

```
read → expand (syntax.ss; Lexpand, expand-lang.ss:74)
     → Lsrc (base-lang.ss:219)
     → cpvalid                     letrec validity checks
     → [cp0 → cptypes → cpletrec] × run-cp0   (default: cp0 twice, cmacros.ss:2336-2339)
     → cpcheck → cpcommonize
     → $np-compile                 (cpnanopass.ss:10842-10886)
         30 passes Lsrc→L1→…→L13   cpnanopass … impose-calling-conventions
         np-after-calling-conventions (cpnanopass.ss:10818-10840)
         13 passes L13.5→…→L16 + register allocator (~10 subpasses)
     → generate-code → code object (c-mkcode, compile.ss:1825-1827)
```

- **Languages:** 28 nanopass languages L1…L16, with fractional names for
  later insertions (`L4.875`, `L4.9375`; `s/np-languages.ss:421-1288`), plus
  `Lsrc`, `Ltype`, `Lexpand` and `Linterp`. Pass definitions: 58
  `define-pass` forms in `cpnanopass.ss`/`cpprim.ss` (including inner
  passes). Primitive expansion is one large pass `L7→L9` (`s/cpprim.ss:106`)
  with 633 `define-inline` handlers. **Holds.**
- **Front end** (`s/compile.ss:1798-1823` for `compile`/`eval`; `:817-842`
  for `compile-file`):
  - cpvalid inserts checks for invalid letrec references;
  - cp0 is the online partial evaluator (§2.2);
  - cptypes does type recovery over an **immutable intmap**
    (`s/cptypes.ss:17-31`), a persistent-data pass inside Chez;
  - cpletrec turns letrec into SCC-sorted `let`/pure `letrec`/`set!`
    (`s/cpletrec.ss:23-47`).
- **REPL eval** compiles each top-level form to a code object through
  exactly this path (`compile` → `$compile-backend` → `c-compile` →
  `$np-compile`, `s/compile.ss:66-74, 1775-1827`). **Holds.**

### 2.2 cp0: inlining with two counters

- **Limits:** `score-limit 20`, the maximum residual size of an integration
  attempt, and `effort-limit 200`, the maximum work per attempt
  (`s/cp0.ss:75-76`). `outer-unroll-limit 0` means recursive procedures are
  not integrated, because doing so "trash[es] cp1's loop recognition"
  (`:77-85`). All three are user parameters
  (`cp0-score-limit`/`cp0-effort-limit`, `:94-112`).
- **Mechanism:**
  - A *scorer* counts residual size and a *watchdog* counts effort
    (`:470-510`). Exceeding either calls `bug-out!`, which resets the
    attempt and **escapes through a one-shot continuation**: `call/1cc` at
    `:2021, 2034`.
  - Watchdogs nest only when the outer one is passive (`new-watchdog`,
    `:494-501`), so effort is charged to the outermost active attempt.
    That bounds total work.
  - Operands are visited lazily and cached per operand record (`:366-380`),
    so the pass is polyvariant (`define-threaded polyvariant #t`).
  - Singly referenced procedures are integrated under a passive scorer, so
    their size does not count against the limit (`:2036-2049`). The header
    comment admits this is "potentially nonlinear" (`:29-35`).
  - Contexts are value/test/effect/app/tail (`context-case`, `:332`).
- **Primitive folding** is a rule table: handlers hang off the primitive
  symbol's property list as `'cp02`/`'cp03`, keyed by optimize level
  (`:2107-2109`). There are 140 `define-inline` forms in cp0.
- This matches *(recalled)* Waddell & Dybvig 1997: online, polyvariant,
  context-sensitive inlining with size and effort counters and abort by
  escape continuation. **Holds** for the source; the paper's exact claims
  are unverified here.

### 2.3 Register allocation and back ends

- **Register allocation** is graph colouring with bit-set conflict graphs
  (`s/cpnanopass.ss:8674-8705`) and a spill-and-retry loop
  (`np-allocate-registers`, `:10582-10696`).
  - Variables are split into spillable and unspillable (temporaries made
    by instruction selection).
  - Call-live variables get frame homes first.
  - Coloring prefers move-related homes (`find-move-related-home`).
  - Poison variables are spilled early once a function has more than 1000
    locals (`:10624`).
  - Instruction selection runs *inside* the allocation loop (`:10660`).
  - Block layout uses likelihood and pariah (cold-path) flags (`:10754`ff).
- **Targets** in `s/`: `x86_64.ss` (3504 lines), `arm64.ss` (3418),
  `riscv64.ss` (2547), `loongarch64.ss`, `ppc32.ss`, `arm32.ss`, `x86.ss`,
  and `pb.ss` (1973). Each defines registers plus 56–65 instructions. A
  native port therefore costs ~2.5–3.5k lines of Scheme plus C glue.
  **Holds.**

### 2.4 pb: why new targets are cheap

- **The machine** (`s/pb.ss:1-80`): 32-bit fixed-width instructions, a
  load/store design "vaguely similar to Arm", 16 integer and 8 FP registers
  (`:72-99`), and a single condition flag. A C interpreter runs it:
  `c/pb.c` (520 lines) plus `c/pb.h` (1130).
- **What makes it cheap:**
  - **Bootstrap:** "a single set of pb boot files can be used to bootstrap
    the compiler for any supported platform" (`pb.ss` header). No
    cross-compiler is needed.
  - **Run anywhere:** a host with a C compiler runs Chez at interpreter
    speed.
  - **AOT to C:** `pbchunk` rewrites pb code objects into C "chunks"
    (`s/pbchunk.ss` header; CSUG `system.stex:1828-1846`).
- So a new target costs nothing to *run*, and only a native back end
  (`*.ss` above) to make it *fast*. Klara's T0 seed on an exotic native host
  is the same idea: one portable bytecode interpreter in C.

### 2.5 Representations

- **Tags:** 3-bit low tags: fixnum `000`, pair, flonum, symbol, closure,
  immediate, typed-object (`s/cmacros.ss:822-829`). Fixnums are 61 bits on
  64-bit machines (`:919-923`). Flonums are boxed in general, but
  `np-unbox-fp-vars!` keeps local flonums unboxed (`cpnanopass.ss:2789`).
- **Closures** are `[code, data…]` (`cmacros.ss:1528-1530`). Closure
  optimization, lifting of well-known closures and SCC identification are
  separate passes (`cpnanopass.ss:1435-2504`).
- **Records** are `[rtd, fields…]` (`:1578-1580`).
- **Continuations are closures** whose code is `nuate`. Fields: `stack`,
  `stack-length`, `stack-clength`, `link`, `return-address`, `winders` and
  `attachments` (`:1568-1576`). Invoking a continuation is a procedure call.
- **Stencil vectors** (`primdata.ss:1768`) and **continuation attachments**
  (`:1914-1916`) were added for Racket, which builds its HAMTs on stencil
  vectors (`racket/src/cs/rumble/hamt-stencil.ss` header).

### 2.6 Racket CS

- `schemify` turns Racket linklets into Chez `lambda`s.
- **Delimited control, marks, parameters and exceptions** live in a Scheme
  layer ("rumble"). Its full continuation is "a chain of metacontinuations,
  each containing a host Scheme continuation, with every prompt on a
  boundary" (`rumble/control.ss:1-60`). It uses Chez's internal operation
  that truncates a captured continuation.
- **Continuation attachments**, a compiler-recognized primitive, made marks
  3–4× faster than a library implementation (paper §4.1).
- **cp0 changes for Racket:** the optimizer was constrained so that it no
  longer rewrites `(let ([x (f)]) x)` to `(f)` when marks or result arity
  could tell the difference.
- **Performance:** Chez-level performance on Scheme benchmarks; slower
  startup (462 vs 269 ms) and longer compile and build times.

## 3. Continuations and effects natively

**How Chez captures** (source-verified; the design is *(recalled)* from
Hieb–Dybvig–Bruggeman 1990 and Bruggeman–Waddell–Dybvig 1996):

- **`call/cc` (multi-shot):** the current stack segment *becomes* the
  continuation, with no copy on capture. A resume copies frames back into
  the live stack, but at most `underflow_limit` bytes. A larger continuation
  is first split at a frame boundary, the upper part stays linked and is
  copied lazily on underflow (`c/schsig.c:55-84` `split`, `:93-140`
  `S_split_and_resize`). A one-shot continuation that must be split is
  promoted to multi-shot (`:48-53`). Resume cost is therefore proportional
  to the frames actually returned through, not to the depth of the
  continuation.
- **`call/1cc` (one-shot):**
  - It carves a fresh segment out of the stack headroom, or takes one from
    the per-thread stack cache, and continues there. Nothing is copied on
    capture or on resume (`cpnanopass.ss:5330-5418`).
  - A used continuation is marked by `shot-1-shot-flag`. An
    "opportunistic one-shot" is merged back into the stack when it is
    contiguous (`cmacros.ss:2182-2192`).
- **No tax on ordinary code.** Every procedure already has its overflow
  check, and loop headers have trap checks (`cpnanopass.ss:3006-3143,
  3997-4012`). Capture adds no instructions to code that never captures.
  **Holds** by inspection.

**Klara on this substrate.** No CPS anywhere on a Chez or segmented-stack
host:

| Klara op class | Realization on Chez | Cost model |
|---|---|---|
| tail-resumptive | direct call through handler evidence (lexical instance = local; ambient = attachment lookup) | a call |
| abort | invoke the one-shot escape continuation of `handle` (exactly cp0's bug-out idiom) | segment switch |
| general, one-shot | prompt = metacontinuation frame at `handle` (rumble design); `perform` captures with `call/1cc`, truncated at the prompt | allocation + segment switch; **Conj ≤ 30 ns** |
| multi-shot (`fork-resume`) | `call/cc`; each resume copies only the frames it returns through | **Conj ≤ 2× hand-written DFS** (JVM CPS: 1.65×) |

Three Klara-specific points:

1. **Copying frames gives snapshot semantics only because Klara locals are
   immutable.** Chez boxes assigned variables (`np-convert-assignments`,
   `cpnanopass.ss:831`), so copies of a frame share those boxes. Scheme
   wants that; G-O6 (per-copy state) does not. Klara's core has no `set!` on
   locals, and world state forks through the world. So G-O6 holds by
   construction on this host, **provided Klara's lowering never introduces
   assigned locals** (obligation I-O5).
2. **Authority footprint check at the second resume.** A stack copy
   duplicates silently. Chez frames carry live masks for the GC
   (`rp-header`), so a frame walker exists and can scan a captured segment
   for authority-tagged values on the *first duplication*. That costs
   O(captured size) once per continuation. JVM CPS gets this from closure
   captures. **Conj.**
3. **C frames are an opaque boundary.** This is the same rule as G §3.2:
   capturing across a foreign callable is a named error, not a promise.

**Comparison.**
- **OCaml 5:** one-shot only, ~1% overhead on effect-free code, handlers
  found by runtime search.
- **Effekt-LLVM:** explicit frames in all effectful code, O(1) prompts,
  copy only on shared resume, non-reentrant.
- **Chez:** both one-shot and multi-shot natively, and no frame discipline
  imposed on compiled code. Its missing piece is lexical prompts; Klara adds
  them with lexical handler instances (G §3.3).

So the answer to "segmented stacks instead of CPS, no tax on non-performing
code" is **yes on native, Conj until measured** (I-O3/I-O4). The JVM keeps
selective CPS.

## 4. Options

### (a) Chez as a host: Klara → Chez source → Chez compiler

| KRI concern | On Chez |
|---|---|
| values, equality, hash | tagged pointers; Klara `=`/hash in Scheme |
| persistent collections | CHAMP/RRB on stencil vectors and records. Racket's HAMT shows this works. **Holds** for feasibility. |
| memory | generational tracing GC. Chez is a **token host** (B §0.3–4): uniqueness comes from region tokens, not RC=1. Perceus-style reuse is not available. |
| world cells, publication | `box-cas!`/`vector-cas!` (`primdata.ss:1181, 1854`), `memory-order-acquire/release` (`:1564-1565`) |
| code: load, guard, invalidate | `compile`/`eval` per definition. Code objects are GC'd heap objects, so unloading is free. Install/invalidate = atomic store into the cell the caller reads (`set-top-level-value!`, `:1726`). Old frames finish on old code, which matches v2 §6 "swap at function entry". No deopt-in-flight; Klara does not need it. |
| control | `call/1cc`, `call/cc`, attachments, engines (timer preemption via the trap register) |
| concurrency | native threads |
| interop | `foreign-procedure`, ftypes |
| observation | Chez's profiler is offline PGO (`compile-profile`, `profile-load-data`, `primdata.ss:1642`). Online counters must be a Klara instrumentation pass (portable). |

- **For:**
  - Months instead of years.
  - Code quality on par with the best native Scheme.
  - Every native target plus pb comes for free.
  - The licence is Apache-2.0, like Klara (`00-design-space.md:40`).
    Vendoring or forking needs only the NOTICE.
- **Against:**
  - The Chez compiler becomes trusted code in every receipt.
  - cp0 re-optimizes Klara's output with its own policy, outside Klara's
    budget and tracking.
  - Compile latency on large forms needs Racket's cutoff.
  - Native memory is tracing, not RC.
  - JVM/JS/Wasm-GC are not covered.

### (b) Reimplement Chez-style passes in Klara (pattern as framework)

- The KRI becomes thin: an emitter for machine code (or LLVM/C via
  metacarp, H) plus the runtime.
- **For:**
  - Every pass is a tracked, certifiable, forkable world value.
  - RC memory on native.
  - One pipeline for all hosts down to K3.
- **Against:**
  - Chez's back end is ~11k (`cpnanopass.ss`) + 8.6k (`cpprim.ss`) + 3.5k
    per architecture lines of tuned Scheme. A pattern-based reimplementation
    starts 25× slower (§5).
  - LLVM is not a baseline back end: it is too slow per function for R2.
    That leaves writing a native code generator from scratch.

### (c) Hybrid: recommended

```
                 portable (Klara code; tracked world values)          per host
 ┌───────────────────────────────────────────────────────────┐  ┌───────────────────┐
 │ expand → K0 ──specialize (cp0-like, world-aware)──► K0'    │  │ JVM: K3=bytecode  │
 │            │      reads: rule set, basis, budget           │  │ JS:  K3=JS        │
 │            ▼                                               │  │                   │
 │          K1 effect-lowered (host-parametric: CPS regions   │  │ Chez/native:      │
 │             only if host.control ≠ :segmented)             │──►  K3 = Lsrc-like   │
 │            ▼                                               │  │  Scheme → Chez    │
 │          K2 specialized (guards, shapes; T2 only)          │  │  cp0(local only)  │
 │            ▼                                               │  │  → np passes      │
 │          K3 dialect per host  ◄── validated by pattern     │  │  → x86/arm/rv/pb  │
 └───────────────────────────────────────────────────────────┘  └───────────────────┘
   T0: sci/Klara interpreter (outer layer of forms > size cutoff, like Racket CS)
   T1: K0 → K3 with var indirection, no cross-cell inlining   (Chez: interaction-env code)
   T2: K0' → K2 → K3 with guards, installed by atomic cell swap
```

- **Phase N1:** Chez is the native host (option a) behind a Klara-owned
  front half.
  - Klara owns everything whose decisions read the world: expansion,
    specialization, cross-definition inlining, effect lowering, guards.
  - Chez owns what is purely local and host-specific: intra-definition
    cp0, closure conversion, register allocation, code generation.
  - Chez's cp0 must never see a world cell as a constant. K3-Chez emits
    cell reads as opaque primitive calls, so the only inlining Chez does is
    of what Klara already proved stable.
- **Phase N2:** move passes from Chez into Klara only on evidence:
  - a pass whose decisions need world reads, guards or certificates;
  - a measured win.
  - **The first candidate is cp0 itself** (§6). The back end stays Chez's.
- **Fork policy:** pin a Chez release (v10.x). Avoid forking the compiler:
  Racket's fork cost years before it merged back. Upstream needed
  primitives (e.g. an authority-aware frame walker) as Racket did.
- **Effect on metacarp/LLVM (H):** they remain the route for certified
  kernels (T3) and RC-managed native code, not the baseline.

## 5. pattern as the pass framework

**What it already expresses.**
- **Dialects** (`def-dialect`, `def-derived` with `+`/`-` of terminals,
  forms and productions; `pattern/src/pattern/nanopass/dialect.clj:419-481`)
  are quoted **values**. That is the right shape for world values.
- **Passes** declare `(=> From To)` (`pass.clj:111`). Typed form-to-form
  rule groups come from `combine-rules` (`pass.clj:33`).
- **Validation:** `validate`/`valid?` (`dialect.clj:637-646`).
- **Boilerplate traversal from a dialect:** `descend-into` (`:657`).
- The test tree contains a 17-pass compiler course and a Scheme→C chain
  with 20 dialects (`test/compiler_course`, `test/scheme_to_c/dialects.clj`).
  Klara's K0–K3 fit this directly:

```clojure
(def-dialect K0
  (terminals [i debruijn?] [c const?] [g global-ref?] [p prim?] [h handler-cap?])
  (Expr [e] ?i (quote ?c) (fn ?n ?e) (?e0 ??e*) (let ?e0 ?e1) (if ?e0 ?e1 ?e2)
            (letrec [??e*] ?e) (resolve ?g) (prim ?p ??e*)
            (perform ?h ?op ??e*) (handle ?hdef ?e) (specialize ?e ?spec)))
(def-derived K1 K0                       ; effect-lowered
  (Expr [e] - (perform ?h ?op ??e*) - (handle ?hdef ?e)
            + (call-evidence ?h ?op ??e*) + (escape ?k ?e) + (prompt ?tag ?e)
            + (capture-1 ?tag ?e) + (capture-n ?tag ?e)))      ; no CPS on :segmented
(def-derived K2 K1
  (Expr [e] + (guard ?assumption ?e ?fallback) + (shape-ref ?s ?slot ?e)
            + (unboxed ?rep ?e)))
(def-derived K3-chez K2                  ; what Chez receives
  (Expr [e] - (specialize ?e ?spec) - (guard ?assumption ?e ?fallback)
            + (cell-read ?g) + (version-check ?w ?e ?e)))
```

**Measured cost** (this note, scratch benchmark).
- **Setup:** pattern `89da31a` on OpenJDK, noisy machine as in the handler
  README. Workload: an 8-rule constant-folding pass, `on-subexpressions`
  over `rule-list`, on a 58,312-node tree, compared against a hand-written
  Clojure `case` pass that gives the same result.
- **Results:**
  - pattern: **3.3–4.3 µs/node**;
  - hand-written: **130–154 ns/node** (25–33×);
  - `valid?` against a 7-production dialect: **2.8–3.2 µs/node**.
- **Against the budget:** a 1000-node definition through 40 passes at
  pattern speed takes ~130 ms, against R2's 5 ms. At hand-written speed it
  takes ~5 ms. **Holds** (measured), as an order of magnitude.

**Why it is slow.**
- `rule-list` tries rules linearly with success/fail continuations through
  a trampoline (`r3/combinators.clj:23-50`).
- `compile-pattern` stages one level: pattern → a tree of closures, not
  code (`match/core.clj:495-540`).

**What has to change before it carries hot passes.**
1. **Generate code, not closures.** Compile a rule set into a decision tree
   (head-symbol switch, then arity, then predicates) and emit Klara/Clojure
   code. This is pattern's own "compiler specializes itself on its rule set",
   done as a *hand-written generating extension* (cogen) for the matcher
   language, not by self-applying a general specializer (§6).
2. **Rules and dialects as tracked world values.** Today dialects live in a
   global atom (`dialect.clj:22`), and re-compilation *mutates the matcher in
   place* (`match/core.clj:530`, documented as experimental). Neither
   records reads or invalidates dependents. The fix is the X1/spindel
   tracking engine: a compiled matcher is a node keyed by (rule-set hash,
   dialect hash), and a rule edit dirties exactly the matchers that read it.
3. **Construction-time checking.**
   - Chez's nanopass builds IR from typed records, so ill-formed output
     fails at construction, at no extra traversal.
   - pattern validates afterwards at ~3 µs/node.
   - Klara IR nodes should be shaped records (D: logical shape ids), with
     form membership as a tag test. Run full `validate` only in test and
     differential modes.
4. **Licence:** pattern's `LICENSE` and `build.clj` say Apache-2.0, but the
   README still says EPL-1.0. Fix the README before Klara depends on it.

**Verdict.**
- Use pattern now for: K0–K3 dialect definitions, validators, the T3 rule
  sets (law-licensed rewrites), and peephole or small passes.
- Write hot T1 passes by hand, or with generated matchers once
  (1) lands and meets I-O6.

## 6. The staging lens

**cp0 is the specializer Klara already wants, minus the world.** Its inputs
map onto §8's binding times:

| cp0 input | Where in Chez | Klara counterpart | Grade |
|---|---|---|---|
| primitive fold/inline handlers | symbol plist `'cp02`/`'cp03` (`cp0.ss:2107-2109`) | rule set with certificate status (F, v2 §7) | stable world value |
| cross-definition unfoldings | `cte-optimization-loc` boxes per machine (`cp0.ss:5801-5847`) | residuals of other definitions, *recorded reads* | static per CodeId if sealed; else guarded (T2) |
| score/effort limits, run twice | `cp0.ss:75-85`, `cmacros.ss:2336` | budget from the §9 predictor ladder; cp0's constants are the "fixed, simple heuristic" top level | per build |
| operand cache (polyvariance) | `operand` records, intra-run (`cp0.ss:366`) | memo nodes keyed (CodeId, context, static args) | cached across runs |
| bug-out | `call/1cc` escape (`cp0.ss:2021`) | an `:abort` op: cheap on every host | — |

Mechanisms and their costs:

1. **Which passes become tracked world values.** Track only at semantic
   boundaries:
   - the expanded core (CodeId);
   - the specializer's residual K0′, keyed (CodeId, basis reads,
     assumptions);
   - K1;
   - the installed executable.

   Make Chez's L1–L16 ephemeral: pure functions of (K3 hash, compiler
   version, host). Cache only the final code object under that key. With
   ~68% of pass time in rebuilding, persisting ~45 intermediate terms per
   definition would cost memory proportional to passes × term size
   (expanding to ~5× after primitive expansion, Keep §3.6.2.2) for no reuse,
   since intermediate IRs are never shared between definitions. Expected
   cost of four tracked boundaries: a few × the source term per definition
   version (**Conj**; I-O7 under R6).
2. **"Compiler specializes itself on its rule set" happens in two places.**
   Pattern matchers (§5.1) and primitive handler tables, which Chez stores
   by name and Klara would store as a rule-set value. Both are first
   Futamura projections of small interpreters (matcher, rule dispatch).
   They are cheap, terminating, and their invalidation is a recorded read
   of the rule set.
3. **Do not expect cp0-style online PE to give the 2nd or 3rd projection.**
   - cp0 terminates by fuel, not by binding-time analysis. Applied to
     itself or to an interpreter, it bugs out exactly where the
     interesting unfolding would be (`outer-unroll-limit 0`).
   - Self-application needs offline BTA or hand-written cogens (Jones et
     al. 1993).
   - The realistic route: a cp0-equivalent written in Klara as the T2
     specializer, with world reads and guards, plus hand-written cogens for
     the two interpreters we care about (matcher, K0 interpreter).
   - This keeps 05 §8's hazard ("early stages must not depend on
     self-specialization") honoured by construction.
4. **Correctness transfer.** s-m-n gives "specialize-then-run ≡ run" once
   the specializer is proved. With Chez's back end in N1, receipts carry
   two parts: certified/tested Klara passes down to K3-Chez, and "trusted:
   Chez v10.x" below. Differential testing against the K0 reference
   interpreter covers the trusted part.

```
 world (tracked)                      ephemeral (pure, cached by hash only)
 ───────────────                      ─────────────────────────────────────
 rule set ─┐                          K3-chez ─► cpvalid ─► cp0(local) ─► … ─► L16 ─► code
 basis  ───┼─► specialize ─► K0' ─► K1 ─► K2 ─┘        key = (hash K3, chez-version, host)
 budget ───┘   (memo: CodeId×ctx×static)          install: CAS cell ← code (guard = version word)
```

## 7. Obligations and falsifiers

| Id | Claim | Status | Falsifier |
|---|---|---|---|
| I-O1 | Chez compiles Klara-lowered definitions of ≤ N nodes within R2 (p99 ≤ 5 ms); above N, interpreting the outer layer (Racket-style) preserves results, effect traces and tail behaviour | **Open** | corpus timing; a size-cutoff program whose observations differ between interpreted and compiled |
| I-O2 | Klara-T1 on Chez (cell indirection, no cross-cell inlining) is within 2× of library-compiled Chez on the same programs | **Open** | r6rs benchmarks compiled both ways |
| I-O3 | One-shot `perform` via `call/1cc` + prompt ≤ 30 ns; perform-free code under a handler runs at 1.00× | **Conj** | port `experiments/handlers` to Chez (counter loop, case iii) |
| I-O4 | Multi-shot enumeration via `call/cc` ≤ 2× hand DFS; SMC beats replay by ≥ 4× | **Conj** | HMM enumeration and SMC on Chez |
| I-O5 | Klara's lowering to Chez introduces no assigned locals, so frame copies give snapshot semantics (G-O6) | **Conj** | grep `set!` on locals in K3-Chez output; a multi-shot test showing shared local state |
| I-O6 | pattern with generated decision-tree matchers ≤ 300 ns/node/pass (today 3.3–4.3 µs) | **Open** | the §5 benchmark rerun |
| I-O7 | Four tracked boundaries keep memory per definition version ≤ 5× its source term and plateau under R6 | **Conj** | 10,000-edit run with heap sampling |
| I-O8 | First-duplication authority scan of a captured segment is sound (finds every authority in live slots) and O(segment) | **Conj** | an authority reachable only from a slot outside the live mask; timing on deep stacks |
| I-O9 | Chez's cp0 never inlines through a world cell in K3-Chez | **Conj** | a REPL edit of a cell whose old value survives in T1 code |

## 8. Questions for Christian

1. **Host or blueprint?** Is Chez the native host (option c, N1), or a design
   to reimplement in Klara (b)? This decides whether metacarp/LLVM is the
   baseline or the T3 route.
2. **Memory on native.** Chez is a tracing, token host. Is giving up
   Perceus reuse on native acceptable for N1, given B's argument that token
   hosts pay more per fork?
3. **Wasm.** Run pb through a C-to-Wasm toolchain (interpreter speed, all of
   Chez), or a WasmGC emitter from K3 (portable, no Chez)?
4. **Trusted base.** Is "trusted: Chez v10.x" in receipts acceptable for N1,
   with differential testing as the only check below K3?
5. **Op classes.** Do tail/abort/general stay a definition-time semantic
   classification on every host (portable, simpler spec), or become a
   cost-model hint where the host has segmented stacks?
6. **pattern investment.** Should matcher code generation (§5.1) and tracked
   rule sets (§5.2) go upstream into `replikativ/pattern`, or should Klara
   keep its own fork?
7. **Pinning.** Update `../ChezScheme` to v10 (`origin/main`). The checked-out
   2020 tree lacks pb, arm64, cpprim and cptypes, and anyone reading it will
   draw wrong conclusions.
