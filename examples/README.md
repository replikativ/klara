# Examples

Each example is a markdown file with the source, REPL transcripts that run
as tests (`clojure -X:test`), what it demonstrates, and which rule of
`doc/semantics.md` or which RFC obligation it exercises. Each file runs in a
fresh REPL session.

<!-- Examples 1–6 (staging) are listed by the staging work; 7–10 below. -->

## Klara-specific examples (`klara/`)

| # | Example | Demonstrates | Exercises |
|---|---|---|---|
| 7 | [SMC with fork and resampling](klara/07-smc.md) | `choose`/`observe` as user effects interpreted by a Klara handler; resampling by resuming one continuation per child; splittable keys; checked against the exact posterior | handler rules `Handle`/`Op`, deep and multi-shot handlers; EF4; AU6 |
| 8 | [A coupled fork: close a shop](klara/08-coupled-fork.md) | a counterfactual in a world fork; one definition under two bases; shared vs split random keys (variance reduction by common random numbers) | snapshot forks (AU4); basis-specific execution; RFC 0001 randomness split |
| 9 | [Redefinition under a running fiber](klara/09-basis-raise.md) | a suspended simulation keeps its basis while the REPL redefines its step function, until it raises at a safe point | fibers, `:world/raise-basis`; gate R4 |
| 10 | [Certified fusion](klara/10-certified-fusion.md) | a map/filter/reduce pipeline fused by an ansatz-proved rewrite, gated by a shape claim, guarded against edits, re-optimized | guarded specialization and certified-rewrite squares; gate R3 |
