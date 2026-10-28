# Evidence and citation ledger

Access date: **2026-10-28**. Main Klara snapshot: **0831749af6a4f72e82501b26feef268ac1ec4b98**, branch `main`. `source-manifest.tsv` records content hashes of the requested local corpus at this base commit. The paper describes S1–S11; concurrently developed S12–S14 worktrees were not inspected or changed. No JVM, proof checker, or benchmark was started for this writing task. LaTeX and PDF checks were run.

## Local evidence → paper claims

| Corpus / entry point | Use in the draft | Evidence boundary |
|---|---|---|
| `README.md`; `doc/guide/README.md`, chapters 01–09 | Language scope and recorded examples | Practitioner documentation, reconciled with milestones where stale |
| `doc/semantics.md`; `spec/README.md` | Rule presentation and proof inventory | Prose checked against the actual definitions below |
| `spec/src/klara/spec/core.clj` | `Tm`, `ev`, `step`, `handleEff`, opening/closing and scope checks | Authoritative small-step definition |
| `spec/src/klara/spec/ws.clj` | `WS`, `WSW`, `WSC`, substitution and scoping infrastructure | De Bruijn scoping, not generated-name freshness |
| `spec/src/klara/spec/props.clj` | `step-det`, `ev-ok`, progress/preservation/safety, `smn`, `run-quote` | Kernel proof source; proof runs are reported by S5, not repeated |
| `spec/src/klara/spec/interp.clj`; `test-spec/`; `spec/test/klara/spec/programs.edn` | Execution adapter, normalization, 69 cases and four differences | Finite differential test; bridge is not verified |
| `examples/klara/07-smc.md`, `08-coupled-fork.md`, `09-basis-raise.md`, `10-certified-fusion.md` | Posterior/normalizer, paired simulation, explicit update points, certified pipeline | Recorded outputs, not new experiments |
| `examples/staging/01`–`06` | Power, matrix/vector, let-insertion, staged interpreter, fusion, regex | Generators have fragment-specific obligations; no universal staging equivalence inferred |
| `doc/architecture.md`; RFCs 0001–0007 | Worlds, authority, effects, licensed specialization, encoding, affine checks, analyzers, nominal abstraction | Architecture/design is not evidence that all paths exist |
| `doc/background/impl/S1.md` | T0/world/host foundation and original tests | Historical milestone |
| S2 | Formal spec, documented in `spec/README.md` | There is no separate `doc/background/impl/S2.md` |
| `S3.md` | Fold laws, certificate boundary, overflow, guard cost | Model equation checked; bridges explicitly trusted |
| `S4.md`, `S5.md` | Runtime staging and mechanized extension | Separate runtime and proof boundaries |
| `S6.md` | Authorities, forks, intents, settlement, fork-resume | Implemented/tests; absent from small-step model |
| `S7.md`, `S8.md`, `S9.md` | Root validity; compile tier; exact frame-state deopt | Installation shape checks and tests, not simulation theorem |
| `S10.md` | Owned cells/loans, local checker, box/array lowering | Narrow fragment; mode distinct from fraction |
| `S11.md`; `experiments/compiler/s11-results.txt`, `s11-profile-after.txt` | Main table and negative entry-overhead result | Reported short/long warmup experiments must stay separate |
| `notebooks/compiler_walkthrough.clj` | Compile-tier user story and validation expectations | Notebook source, not rerun |

Research-note synthesis used when choosing the paper's scope:

- **A:** operational core versus the proposed tree/monoidal-computer model; no full denotational adequacy result yet.
- **B:** persistent data versus owned representation; sharing, freezing, and storage have distinct lifetime obligations.
- **C:** explicit staging, binding-time grades, dependencies, and generator-correctness obligations.
- **D:** dispatch/interop facts depend on host semantics; opaque behavior is a boundary.
- **E:** inference/evidence, budgets, learning and selection need explicit accounting.
- **F:** standard-library, matching, laziness and host-callback choices affect effect boundaries.
- **G:** lexical capabilities and continuation implementation choices; its early Klara status table is historical.
- **H, N:** native ownership/region lessons; N corrects H's Carp capture and IR assumptions. No claim that native integration is already implemented.
- **I:** baseline compilation, nanopass costs, interactive lookup, and the role of host compilers.
- **J:** static facts are relative to a reference semantics and basis; unknown effects/escapes must remain conservative.
- **K, M:** root-keyed validity and exact deopt frame states; several “missing” mechanisms were subsequently implemented in S7–S11.
- **L:** browser/JS/Wasm paths are proposals, not current portable-runtime results.
- **O:** languages as libraries, tracked descriptors, and staged Datalog are a longer-term language-extension story.
- **P:** specification culture, ML abstraction contracts, staging scope versus legal motion, and persistence boundaries.

Selected adjacent code/documentation: `lambda-join/papers/esop27-joins/main.tex`, `redex/README.md`, `lean/LambdaJoin/Core.lean`, and `studies/koka.md`; ansatz's kernel/proof interface documentation; Spindel, SCI, Raster, Wandler, Foerster and Datahike READMEs; BER MetaOCaml's `typing/trx.ml`; OCaml's `stdlib/effect.mli`; Racket's README and the language-extension references in O. These are context and comparative evidence; none was rebuilt or modified. The paper does not inherit their proofs or performance results.

## Bibliography verification

Every key in `references.bib` is accounted for below. Bibliographic titles/authors/years/venues were verified from a publisher, author, institutional repository, or official project source. Local notes and Zotero served as discovery aids, not the sole authority. Unneeded page ranges/DOIs were omitted rather than guessed; where a range was not established, PDF page counts supply `numpages`. The undated Unison entry explicitly uses `n.d.`.

| Key | Verified publication identity | Primary verification source |
|---|---|---|
| `plotkin2009` | Gordon Plotkin, Matija Pretnar. *Handlers of Algebraic Effects*. ESOP 2009, LNCS 5502, 80–94. | [Edinburgh publication record](https://www.research.ed.ac.uk/en/publications/handlers-of-algebraic-effects/), [author PDF](https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf) |
| `effekt2020` | Jonathan Immanuel Brachthäuser, Philipp Schuster, Klaus Ostermann. *Effects as Capabilities: Effect Handlers and Lightweight Effect Polymorphism*. PACMPL 4, **OOPSLA**, article 126, 2020. | [Institutional paper](https://infoscience.epfl.ch/bitstreams/d8c0cff1-6103-46c7-acb6-c9cc3dbb2704/download) |
| `koka2021` | Ningning Xie, Daan Leijen. *Generalized Evidence Passing for Effect Handlers: Efficient Compilation of Effect Handlers to C*. PACMPL 5, ICFP, article 71, 2021. | [Author's published PDF](https://xnning.github.io/papers/multip.pdf), [Microsoft record](https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers-or-efficient-compilation-of-effect-handlers-to-c/) |
| `ocaml2021` | KC Sivaramakrishnan, Stephen Dolan, Leo White, Tom Kelly, Sadiq Jaffer, Anil Madhavapeddy. *Retrofitting Effect Handlers onto OCaml*. PLDI 2021, 206–221. | [Author paper page](https://anil.recoil.org/papers/2021-pldi-retroeff/), [preprint](https://arxiv.org/abs/2104.00250) |
| `metaml2000` | Walid Taha, Tim Sheard. *MetaML and Multi-stage Programming with Explicit Annotations*. Theoretical Computer Science 248(1–2), 211–242, 2000. | [Publisher record](https://www.sciencedirect.com/science/article/pii/S0304397500000530) |
| `ber2014` | Oleg Kiselyov. *The Design and Implementation of BER MetaOCaml—System Description*. FLOPS 2014, LNCS 8475, 86–102. | [Author project/publication page](https://okmij.org/ftp/ML/MetaOCaml.html), [full version](https://okmij.org/ftp/meta-programming/ber-design.pdf) |
| `lms2010` | Tiark Rompf, Martin Odersky. *Lightweight Modular Staging: A Pragmatic Approach to Runtime Code Generation and Compiled DSLs*. GPCE 2010. | [Author publication list](https://tiarkrompf.github.io/publications.html) distinguishes GPCE 2010 from CACM 2012 |
| `amin2018` | Nada Amin, Tiark Rompf. *Collapsing Towers of Interpreters*. PACMPL 2, POPL, article **52**, 2018. | [Author's published PDF](https://namin.seas.harvard.edu/pubs/popl-collapsing-towers.pdf), [Cambridge record](https://www.repository.cam.ac.uk/items/433c94c6-d72d-44a6-88b2-4cb069b460bf) |
| `racket2011` | Sam Tobin-Hochstadt, Vincent St-Amour, Ryan Culpepper, Matthew Flatt, Matthias Felleisen. *Languages as Libraries*. PLDI 2011. | [Author-hosted proceedings PDF](https://www-old.cs.utah.edu/plt/publications/pldi11-tscff.pdf) |
| `truffle2013` | Thomas Würthinger, Christian Wimmer, Andreas Wöß, Lukas Stadler, Gilles Duboscq, Christian Humer, Gregor Richards, Doug Simon, Mario Wolczko. *One VM to Rule Them All*. Onward! 2013. | [Graal project bibliography](https://www.graalvm.org/jdk21/community/publications/), [official program](https://2013.splashcon.org/details/onward-2013-papers/6/One-VM-to-Rule-Them-All) |
| `clojure2020` | Rich Hickey. *A History of Clojure*. PACMPL 4, HOPL, **2020**. | [Author's history page](https://clojure.org/about/history), DOI 10.1145/3386321; conference talk was 2021, publication was 2020 |
| `unison` | Unison Computing. *The Big Idea*. Undated project documentation, accessed 2026-10-28; **not a research publication**. | [Official documentation](https://www.unison-lang.org/docs/the-big-idea/) |
| `iris2018` | Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars Birkedal, Derek Dreyer. *Iris from the Ground Up: A Modular Foundation for Higher-order Concurrent Separation Logic*. JFP 28, e20, 2018. | [Institutional publication record](https://pure.mpg.de/view/item_3033720), [published PDF](https://pure.mpg.de/pubman/item/item_3033720_3/component/file_3331878/iris-from-the-ground-up-a-modular-foundation-for-higher-order-concurrent-separation-logic.pdf?mode=download) |
| `boyland2003` | John Boyland. *Checking Interference with Fractional Permissions*. SAS 2003, LNCS 2694, 55–72. | [Author's institutional bibliography](https://uwm.edu/engineering/directory/boyland-john/) |
| `staton2016` | Sam Staton, Hongseok Yang, Chris Heunen, Ohad Kammar, Frank Wood. *Semantics for Probabilistic Programming: Higher-order Functions, Continuous Distributions, and Soft Constraints*. LICS 2016, 525–534. | [Institutional publication record](https://www.research.ed.ac.uk/en/publications/semantics-for-probabilistic-programming-higher-order-functions-co/), [published institutional PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/25273011/Staton_et_al_2016_Semantics_for_Probabilistic_Programming.pdf) |
| `cakeml2014` | Ramana Kumar, Magnus O. Myreen, Michael Norrish, Scott Owens. *CakeML: A Verified Implementation of ML*. POPL 2014. | [Project paper](https://cakeml.org/popl14.pdf), [project BibTeX](https://www.cakeml.org/publications_bib.html) |
| `watt2018` | Conrad Watt. *Mechanising and Verifying the WebAssembly Specification*. CPP 2018. | [Author-hosted PDF](https://www.cl.cam.ac.uk/~caw77/papers/mechanising-and-verifying-the-webassembly-specification.pdf), [Cambridge record](https://www.repository.cam.ac.uk/items/c067305e-98f4-40da-a5b0-a731f58a049e) |
| `joinsdraft` | *Every Join Has a Base: Merging What Forked Computations Learned*, local v0.3 dated 2026-10-08. **Unpublished; anonymous author line.** Project-level attribution only. | Local `../lambda-join/papers/esop27-joins/main.tex`; no venue publication or acceptance verified |

Corrections during verification: the Zotero Staton entry has an early-draft author order with Wood third; the published record places Wood last. The Purdue Amin–Rompf preprint has placeholder DOI/article 33; the author's published version gives DOI 10.1145/3158140 and article 52. The Koka author-site final PDF uses a colon subtitle, whereas the MSR record uses “(or, …)”; the bibliography follows the final PDF. RFC 0002's ICFP attribution for the 2020 capability paper is not used.

## Personal literature consultation

The database was first copied from the requested Zotero location into ignored `paper/tmp/zotero.sqlite`; only that copy was queried. `items` joined to `itemData`, `itemDataValues`, and `fields` supplied title/date/abstract/publication/DOI metadata. `itemCreators` joined to `creators` supplied ordered names. Relevant local entries include 3430 (Amin–Rompf), 14388 (Hickey), 14781 (Staton et al.), and 10346/10350 (Pavlovic's monoidal-computer papers). Abstracts were consulted where available. They are not republished here.

Reproducible core queries (run against the **copy**, not the live database):

```sql
SELECT i.itemID, f.fieldName, v.value
FROM items AS i
JOIN itemData AS d ON d.itemID = i.itemID
JOIN fields AS f ON f.fieldID = d.fieldID
JOIN itemDataValues AS v ON v.valueID = d.valueID
WHERE f.fieldName IN
  ('title','date','abstractNote','publicationTitle','DOI');

SELECT ic.itemID, ic.orderIndex, c.firstName, c.lastName
FROM itemCreators AS ic JOIN creators AS c ON c.creatorID = ic.creatorID
ORDER BY ic.itemID, ic.orderIndex;
```

Text searches in the requested zetteldeft tree located the Sam Staton, monoidal-computer, MCMC, and linearity/uniqueness notes. The monoidal-computer note linked Pavlovic's computability and complexity papers and helped identify the intended categorical direction. No private note text, Zotero database, attachment, or library export is committed. Those pointers do not establish the conjectural model in the paper.

Pagination cross-checks: [LMS proceedings PDF](https://infoscience.epfl.ch/record/150347/files/gpce63-rompf.pdf) (10 pages), Racket PDF (10), Watt PDF (13); [Truffle institutional record](https://research.jku.at/en/publications/one-vm-to-rule-them-all/) (187–204); [CakeML institutional record](https://researchportalplus.anu.edu.au/en/publications/cakeml-a-verified-implementation-of-ml-2/) and project bibliography (179–192). Hickey’s published article identifies itself as article 71, 46 pages.
