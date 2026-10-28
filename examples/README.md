# Examples

Each example is a markdown file with the source, REPL transcripts that run
as tests (`clojure -X:test`), what it demonstrates, and which rule of
`doc/semantics.md` or which RFC obligation it exercises. Each file runs in a
fresh REPL session.

## Staging examples (`staging/`)

Chapter 5 of the guide (`doc/guide/05-staging.md`) explains the forms.

| # | Example | Demonstrates | Exercises |
|---|---|---|---|
| 1 | [power](staging/01-power.md) | the residual `(fn [y] (* y (* y ...)))`; squaring with `genlet`; code size with and without it | `code`/`esc`/`run`; hygiene; let-insertion |
| 2 | [dot product and matrix-vector product](staging/02-matrix-vector.md) | loop unrolling and dropping zeros for a statically known matrix; each vector element loaded once | implicit `lift` (CSP); code built in host callbacks; memoized `genlet` |
| 3 | [fib and gibonacci with let-insertion](staging/03-fib-let-insertion.md) | exponential duplication vs linear code; a generated `letfn` group (gibonacci, Ackermann) | `genlet`, `with-genletrec`; scope check for let-inserted names |
| 4 | [a staged interpreter yields a compiler](staging/04-staged-interpreter.md) | one stage-polymorphic evaluator for a tiny Lisp, as interpreter and as compiler (first Futamura projection) | obligation O10 (C-staging); generated recursive fns |
| 5 | [stream fusion](staging/05-stream-fusion.md) | strymonas-style `range`/`map`/`filter`/`take`/`fold` generating one loop; relation to S3's certified fusion | scope check across cooperating generators |
| 6 | [regex matcher specialization](staging/06-regex.md) | Pike's backtracking matcher specialized to a pattern; partially static positions | `recur` through spliced code; `genlet` |

## Klara-specific examples (`klara/`)

| # | Example | Demonstrates | Exercises |
|---|---|---|---|
| 7 | [SMC with fork and resampling](klara/07-smc.md) | `choose`/`observe` as user effects interpreted by a Klara handler; resampling by resuming one continuation per child; splittable keys; checked against the exact posterior | handler rules `Handle`/`Op`, deep and multi-shot handlers; EF4; AU6 |
| 8 | [A coupled fork: close a shop](klara/08-coupled-fork.md) | a counterfactual in a world fork; one definition under two bases; shared vs split random keys (variance reduction by common random numbers) | snapshot forks (AU4); basis-specific execution; RFC 0001 randomness split |
| 9 | [Redefinition under a running fiber](klara/09-basis-raise.md) | a suspended simulation keeps its basis while the REPL redefines its step function, until it raises at a safe point | fibers, `:world/raise-basis`; gate R4 |
| 10 | [Certified fusion](klara/10-certified-fusion.md) | a map/filter/reduce pipeline fused by an ansatz-proved rewrite, gated by a shape claim, guarded against edits, re-optimized | guarded specialization and certified-rewrite squares; gate R3 |
