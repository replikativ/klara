You are an expert critic and constructive collaborator reviewing the first design
iteration of **Klara**, a new Lisp language in the replikativ open-source stack.
The designer is Christian Weilbach (PhD in probabilistic programming). He wants hard,
honest, constructive criticism: find contradictions, missing pieces, overreach, and
better alternatives from the literature, and propose concrete fixes.

Read, in this order (all under /home/christian-weilbach/Development/lambda-join/doc/klara/):
1. 00-design-space.md — principles and decisions so far
2. 01-core-v1.md — the synthesized design (the main object of review; §11–13 are the latest decisions)
3. research/A-core-calculus.md, B-memory-model.md, C-staging.md, D-dispatch-interop.md,
   E-resources-learning.md — the research notes it synthesizes

You may read any code under /home/christian-weilbach/Development/ to check claims, notably:
lambda-join/v0/src/v0/ (the current implementation: kernel.clj, expand.clj, world.clj, defs.clj,
dispatch.clj), lambda-join/doc/*.md (prior design), lambda-join/redex/, lambda-join/lean/,
raster/, spindel/, partial-cps/, metacarp/, carpaccio/, wandler/, ansatz/, gatlab-clj/ (katzen),
foerster/, datahike/, yggdrasil/, ber-metaocaml/, and the Clojure source in clojure/ (for
interop questions only).

You may search the web for papers, and you may query Christian's Zotero library: the database is
/home/christian-weilbach/snap/zotero-snap/common/Zotero/zotero.sqlite (copy it into
/home/christian-weilbach/Development/lambda-join/doc/klara/reviews/tmp/ first because Zotero may
hold a lock; query items/itemData/itemDataValues/fields for titles and abstracts; attachments are
under .../Zotero/storage/). Prefer primary sources and cite them with URLs or Zotero titles.

Review along these axes, leading with the most serious problems:
1. **Soundness and coherence**: do the sections contradict each other (core calculus vs sorts vs
   staging vs dispatch vs grades)? Is the 12-form untyped core with deep handlers, dynamic sort
   tags, and the "MC of data acting on a linear world" coherent? Is the adequacy statement right?
2. **Feasibility and cost**: especially effect handlers and continuations on the JVM (no native
   continuations), multi-shot continuations for inference, world lookups on every global read,
   sort tags on every object, region tokens. Where will performance break?
3. **The narrowing doctrine** ("annotations never change meaning"; checked claims throw; hints
   fall back): is it consistent with dispatch patterns, representation licences, `within ε`
   refinement and convergent meaning (§12)?
4. **Staging/"macros as two constructs"** (§13): is the split into staged functions and syntax
   extensions sound and sufficient? Compare to Racket, Lean 4 elaborators, Scala 3 quotes,
   MetaOCaml, Template Haskell.
5. **What is missing**: concurrency and parallelism model, error/condition system, module system
   and namespaces under content addressing, I/O and irreversible effects, debugging/observability,
   security/capabilities, numerics. Which omissions are fatal for v1?
6. **Alternatives the design overlooked**: languages or papers that already solved parts of this
   (e.g., Koka, Effekt, Eff, Unison abilities, Lean 4, Racket, Julia, Truffle, Hylo, Verse,
   Granule, Links, Frank, Multicore OCaml, Scheme48/Chez, Self). Be specific about what to take.
7. **Positioning**: will this satisfy both PL researchers and pragmatic Clojure users? What would
   each audience reject first?
8. **Concrete recommendations**: a prioritized list of changes to 01-core-v1.md, each with
   rationale, and a list of experiments that would most reduce uncertainty.

Write your review to
/home/christian-weilbach/Development/lambda-join/doc/klara/reviews/codex-astra-critic.md
(about 3000–5000 words, markdown, sections per axis, each issue rated severity
high/medium/low, with file:line references and citations). Do not modify any other files.
Finish by printing a 15-line summary of your top findings.
