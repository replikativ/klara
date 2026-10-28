# Klara paper discussion draft

Read [main.pdf](main.pdf) first. It is an 19-page internal OOPSLA-style research draft for Christian Weilbach, grounded in the main checkout through S11 (`0831749af6a4`). The recommended target is **OOPSLA 2027 Round 2, 7 April 2027 AoE**; see [VENUE.md](VENUE.md) for verified dates and alternatives.

The paper develops the design around shared computation and accounted authority, then presents examples, small-step rules and their mechanized status, a pure big-step equivalence sketch, a restricted weighted-tree interpretation, resource/affine obligations, implementation, recorded measurements, and related work. The [issue list](ISSUES.md) contains the larger design and documentation questions. [SOURCES.md](SOURCES.md) records citation verification and local evidence; [source-manifest.tsv](source-manifest.tsv) pins the input corpus.

## Build

From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Or from the repository root:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/main.tex
```

Dependencies: TeX Live with `acmart`, `mathpartir`, `stmaryrd`, `listings`, `tikz`, `xurl`, `anyfontsize`, BibTeX and `latexmk` (including the fonts required by acmart). Listings use a local Clojure/Klara style, so **shell escape and Pygments are not required**. `main.pdf` is committed for immediate reading; auxiliary files and `paper/tmp/` are ignored.

Review formatting uses `acmsmall,screen,review,nonacm`, with named internal authorship. Before submission, adapt to the venue's current anonymous format and review the data-availability/AI-use statements. This is a discussion draft, not an approved submission.

## Verification and provenance

The build uses pdflatex/BibTeX through latexmk. Final validation checks for undefined citations/references, layout overflow, and unresolved LaTeX warnings, and visually inspects representative pages. No JVM was started. The examples, proof checks, and benchmark outputs are **recorded repository evidence**, not fresh runs. New big-step and finite-tree arguments are labeled separately from kernel-checked theorems; denotational adequacy, authority soundness, and full compiler refinement remain open.

The private Zotero copy and temporary PDF renders live only in `tmp/`. Do not add that directory to an artifact or commit. No sibling worktree was changed. Small corrections are limited to `doc/`; larger RFC/spec/runtime/example issues are listed rather than silently redesigned.
