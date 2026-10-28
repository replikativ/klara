# Venue recommendation — checked 28 October 2026

**Target OOPSLA 2027, Round 2, 7 April 2027 (AoE).** The language-design contribution is the interaction of forkable worlds, lexical effects, authority accounting, and optimization—not a standalone staging trick. OOPSLA is a good home for that combination of semantics and an implemented language. April leaves time for a small authority theorem and a credible evaluation. This is a recommendation, not a claim that the current draft is submission-ready. The [official call](https://2027.splashcon.org/track/splashoopsla2027) confirms the date and review format.

The strongest alternative is ICFP if the work becomes primarily a semantics/staging paper; ECOOP is plausible if ownership and runtime integration become central. ⟨Programming⟩ is attractive if the contribution becomes an evaluated account of interactive programming practice. PLDI is a good subject fit but its imminent deadline leaves too little time for the missing evidence.

## Deadline survey

Dates below are submission dates, not conference dates. “Passed” is relative to 2026-10-28. AoE means UTC−12. Standing journal cycles and unannounced dates are distinguished from explicit 2027 calls; no date was inferred from a previous conference year.

| Venue | Submission deadline(s) | Status | Fit and practical implication | Primary source |
|---|---|---|---|---|
| **OOPSLA 2027** | R1 **2026-10-14**; R2 **2027-04-07**, AoE | R1 passed; R2 available | Best overall language + semantics + implementation fit; recommended R2 | [2027 CFP](https://2027.splashcon.org/track/splashoopsla2027) |
| PLDI 2027 | **2026-11-12**, AoE | Available, very soon | Needs a stronger implementation contribution and evaluation than this snapshot supplies | [2027 CFP](https://pldi27.sigplan.org/track/pldi-2027-papers) |
| ICFP 2027 | **2027-02-25**, AoE | Available | Excellent for effects/staging and an authority calculus; earlier than recommended target | [2027 CFP](https://icfp27.sigplan.org/track/icfp-2027-icfp-papers) |
| POPL 2027 | **2026-07-09**, AoE | Passed | Future cycle only; would need a sharper foundational result | [2027 CFP](https://popl27.sigplan.org/track/POPL-2027-popl-research-papers) |
| ECOOP 2027 | R1 **2026-11-19**; R2 **2027-02-11**, AoE | Both available | Ownership, capabilities, dynamic language implementation; a realistic R2 alternative | [2027 CFP](https://2027.ecoop.org/track/ecoop-2027-technical-papers) |
| ESOP 2027 | R1 **2026-05-28**; R2 **2026-10-15** | Both passed | Good theory/practice fit, but no remaining 2027 submission round | [2027 CFP](https://etaps.org/2027/conferences/esop/) |
| PEPM 2027 | **2026-10-23**, AoE | Passed | Strong fit for a narrower staged-interpreter/check-movement paper; workshop 2027-01-12 | [2027 CFP](https://popl27.sigplan.org/home/pepm-2027) |
| Onward! 2027 | **Not announced/verified** | Unknown | Suitable if the paper emphasizes a new programming perspective; do not schedule against a guessed date | [SIGPLAN series page](https://www.sigplan-pages.sigplan.hosting.acm.org/Conferences/Onward/), [SPLASH 2027 tracks](https://2027.splashcon.org/) |
| ⟨Programming⟩ journal | **February 1, June 1, October 1**, AoE, recurring | Published standing cycle; calendar-2027 dates follow that rule, not a separate dated CFP | Strong alternative for programming experience plus system design; journal cycle is not the same as the 2027 conference attendance deadline | [Journal timeline](https://programming-journal.org/timeline/) |

## Format and preparation

The draft uses `acmart` with `acmsmall,screen,review,nonacm`, named authorship for internal review, mathpartir, semantic brackets, Clojure-style listings, and TikZ. OOPSLA requests `acmsmall,screen,review,anonymous`; the initial main-text limit is 23 pages, excluding required statements, bibliography, and supplementary material. The internal `nonacm` option removes publication boilerplate. Before actual submission, enable anonymity, remove internal provenance that identifies the author, and follow the current call's required statements and reviewer policies. [OOPSLA format and submission rules](https://2027.splashcon.org/track/splashoopsla2027).

The present draft is comfortably within the main-text allowance. It contains data-availability and AI-use statements for discussion; author review and an archival artifact are still needed. Confirm venue rules again before submitting. Do not submit substantially overlapping versions concurrently.

Suggested work before April: formalize a sequential authority fragment; connect its store invariant to the affine erasure checker; force deoptimization at every supported checkpoint; repeat performance experiments across independent processes with hardware/JVM details; measure fork/edit/adopt latency and memory retention on a realistic workload. These are our research priorities, not requirements copied from a venue call.
