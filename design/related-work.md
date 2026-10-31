# Related work

Short notes on the work Klara builds on, and what Klara adds. Citations were
checked against the publisher, arXiv or official documentation.

## Staging

- **MetaML.** Taha and Sheard, *Multi-Stage Programming with Explicit
  Annotations*, PEPM 1997 ([doi](https://doi.org/10.1145/258993.259019));
  journal version TCS 248, 2000 ([doi](https://doi.org/10.1016/S0304-3975(00)00053-0)).
  Brackets, escape, run and lift; free present-stage values may appear in
  later-stage code (cross-stage persistence, CSP). Klara's `code`, `esc`,
  `run` and `lift` are these operations.
- **BER MetaOCaml.** Kiselyov, FLOPS 2014 ([doi](https://doi.org/10.1007/978-3-319-07151-0_6)),
  [documentation](https://okmij.org/ftp/ML/MetaOCaml.html). Serializable CSP
  values become literals; others are kept by reference, so code holding them
  runs in-process but cannot be printed faithfully. Klara's `lift` behaves the
  same way. Klara's links make *global* references printable and portable
  between worlds, which MetaOCaml does not need because it has a single
  global environment.
- **CSP is not lifting.** Hanada and Igarashi, *On Cross-Stage Persistence
  in Multi-Stage Programming*, FLOPS 2014
  ([pdf](https://www.fos.kuis.kyoto-u.ac.jp/~igarashi/papers/pdf/csp-flops2014.pdf)).
  Embedding a value and turning it into syntax coincide only for base values.
  Klara keeps them as two operations: `lift` embeds, `reify` builds
  structure.
- **Scope extrusion with effect handlers.** Lee, Xie, Kiselyov and Yallop,
  *Handling Scope Checks*, POPL 2026 ([arXiv](https://arxiv.org/abs/2601.18793)).
  A formal comparison of dynamic scope-extrusion checks in a language with
  effect handlers, including a check proved correct. Klara checks extrusion
  dynamically, when `code` completes and when `run` starts; this paper is the
  reference for making that check precise.
- **Semantics-preserving staging.** Tan and Wei, *When Do Staging
  Annotations Preserve Semantics?*, OOPSLA 2026 ([arXiv](https://arxiv.org/abs/2606.30854)).
  Mechanized proof, for two typed stages with let-insertion as a control
  effect, that generated code is equivalent to the program with annotations
  erased. Klara does not rely on such a theorem: it checks each generated
  candidate against its reference. The two approaches are complementary: a
  staging discipline with this theorem could skip the check.
- **Refined environment classifiers.** Kiselyov, Kameyama and Sudo, APLAS
  2016. A static discipline against scope extrusion even through mutable
  cells. A possible future static layer.

## Binding, phases and modules

- **Racket phases.** Flatt, *Composable and Compilable Macros*, ICFP 2002
  ([doi](https://doi.org/10.1145/581478.581486)) and *Binding as Sets of
  Scopes*, POPL 2016 ([doi](https://doi.org/10.1145/2837614.2837620)). A
  global binding's identity is module, symbol and phase, and each phase has
  its own instance of a module. Klara's link is the analogous identity for
  worlds: world, qualified name, and (for guarded links) generation. Klara's
  stages are relative to `code` nesting, not phases of module instantiation;
  macro expansion is a separate phase.
- **Content-addressed code.** Unison ([the big idea](https://www.unison-lang.org/docs/the-big-idea/),
  [update](https://unison-lang.org/docs/ucm-commands/update)). Definitions are
  identified by the hash of their syntax tree, so every reference is
  effectively pinned, and updates re-point names in the codebase tooling.
  Klara takes the opposite default (late links, as in Clojure) and makes
  pinning explicit and available at run time.
- **Darklang** ([blog, 2019](https://blog.darklang.com/how-dark-deploys-code-in-50ms/)).
  Function versions and gradual migration of callers. A design blog, not a
  formal account.

## Live update

- **Erlang** ([code loading](https://www.erlang.org/doc/system/code_loading.html)).
  At most two versions of a module, current and old; qualified calls go to
  current code; loading a third version purges the old one and kills
  processes still running it. This is a bounded-memory policy for code
  versions. Klara's activations play the role of processes, `world/advance`
  the role of a qualified call, and the lifetime design of
  [01-lifetimes.md](01-lifetimes.md) makes retention follow reachability
  rather than a fixed count.
- **Dynamic software updating.** Hicks and Nettles, TOPLAS 2005
  ([doi](https://doi.org/10.1145/1108970.1108971)). Type-safe patches to a
  running C-like program. Klara's worlds make the old and new versions
  coexist as values rather than patching in place.

## Space safety

- Clinger, *Proper Tail Recursion and Space Efficiency*, PLDI 1998
  ([doi](https://doi.org/10.1145/277650.277719)). Defines proper tail
  recursion and safe-for-space as space-complexity properties of an abstract
  machine. Klara's `L0.space.*` rules follow it.
- Morrisett, Felleisen and Harper, *Abstract Models of Memory Management*,
  FPCA 1995 ([pdf](https://www.cs.cmu.edu/~rwh/papers/gc/fpca95.pdf)). Garbage
  collection as a rewriting rule, so its correctness can be proved. The model
  for stating Klara's collectability obligations formally.
- Flatt and Findler, *Safe-for-Space Linked Environments*, 2025
  ([doi](https://doi.org/10.1145/3759427.3760379)). Space safety for a linked
  environment interpreter by making the collector traverse environments.
  Relevant if Klara's frames move from per-term environments to linked ones.
- Hillerström, Lindley and Atkey, *Effect Handlers via Generalised
  Continuations*, JFP 2020 ([doi](https://doi.org/10.1017/S0956796820000040)).
  A CEK machine for deep and shallow handlers. We found no published
  safe-for-space result for multi-shot handlers: an open question Klara
  runs into directly.

## Checking optimizer output

- Pnueli, Siegel and Singerman, *Translation Validation*, TACAS 1998
  ([doi](https://doi.org/10.1007/BFb0054170)). Validate each compiler run
  instead of verifying the compiler.
- Necula, *Translation Validation for an Optimizing Compiler*, PLDI 2000
  ([doi](https://doi.org/10.1145/349299.349314)). Checks gcc's optimizations
  by symbolic evaluation and an inferred simulation relation.
- Klara's checker is a translation validator whose equivalence is
  definitional unfolding, as in a proof assistant's kernel. That makes it
  small, makes its rules individually provable, and lets untrusted guest code
  (or an agent) be the optimizer.

## What Klara adds

1. **World-relative links in staged code.** Code carries late, pinned or
   guarded links, so `run (reify f)` preserves `f` even when `f` belongs to
   an older world, and AOT compilation is pinning.
2. **Staged generators as checked optimizers.** An ordinary generator becomes
   an optimization recipe whose output is admitted only after translation
   validation against a reference.
3. **Compilation as a budgeted, isolated job.** Preparation, checking and
   their costs are ordinary values in the language, not runtime internals.
4. **Lifetimes for versioned programs.** Named roots, footprint slices and
   collectability obligations aimed at bounded memory in a system that keeps
   old versions on purpose.
