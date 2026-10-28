# The Klara guide

<!-- The guide agent owns this file except for the section "Transcripts"
     below, which documents the format checked by test/klara/transcript_test.clj. -->

This guide explains Klara through examples you can run. Each chapter goes
from **syntax** to **meaning** (informally, citing the rule in
`../semantics.md` or the obligation in an RFC where one exists) to **REPL
transcripts**. Every transcript is a test: `clojure -X:test` runs them
against the real REPL, so what you read is what Klara does today.

Each chapter ends with what is *not* implemented. Blocks tagged
`klara-repl :norun` show design that cannot run yet, and say why.

## Chapters

| # | Chapter | What you learn | Status |
|---|---|---|---|
| 1 | [The core](01-core.md) | values, functions, the twelve core forms, how Clojure syntax expands into them, code identity | implemented (T0) |
| 2 | [The world](02-world.md) | definitions, recorded reads, redefinition at the REPL, the pending state, bases | implemented |
| 3 | [Effects](03-effects.md) | `perform`/`handle`, lexical vs ambient handlers, state, generators, `choose`/`observe`, exceptions, the host boundary | implemented; operation classes are design |
| 4 | [Forks and authority](04-forks.md) | snapshot forks, fork-resume, the authority model of RFC 0001 | forks implemented; authority is design |
| 5 | [Staging](05-staging.md) | code values, `code`/`esc`/`run`/`lift`, let-insertion | implemented (written by the staging work) |
| 6 | [Certified optimization](06-certified-optimization.md) | the specialization cache, guards, shape claims, fusion with ansatz certificates | implemented for map/filter/reduce |
| 7 | [Clojure interop](07-clojure-interop.md) | calling Clojure and Java, linked vs hosted code, the naming rule, Tier H quirks | partly implemented |

## How to read it

- **Clojure programmers:** 1, 2, 3, 7, then the examples. Most of the
  syntax is Clojure's; the differences are the world (chapter 2) and
  effects (chapter 3).
- **PL researchers:** 1 and 3 with `../semantics.md` open beside them,
  then 4 and 6. `../architecture.md` §8 states each correctness claim as a
  commuting square and gives its status.
- **LLMs and tools:** the top-level `README.md`, then `../semantics.md` for
  the rules, then the chapters in order. Transcripts are exact: the line
  after a `k=>` form is the REPL's output, byte for byte.

Worked examples beyond the chapters are in `../../examples/`
(`examples/klara/` for SMC, coupled forks, basis raise and certified
fusion).

## Running

```
clojure -M:repl      # the Klara REPL, prompt k=>
clojure -X:test      # all tests, including every transcript in the guide and examples
```

A bare keyword at the prompt is a REPL command (`:help`, `:world`,
`:basis`, `:fork name`, `:switch name`, `:expand form`, `:code form`).

## Transcripts

REPL sessions in this guide and under `examples/` are tests. `clojure -X:test`
runs them through `klara.transcript-test`, using the same reader, evaluator
and printer as the REPL (`clojure -M:repl`).

A transcript is a fenced code block whose info string is `klara-repl`:

````markdown
```klara-repl
k=> (def sq (fn [x] (* x x)))
#'sq
k=> (map sq [1 2 3])
(1 4 9)
k=> (let [y 2]
        (sq y))
4
```
````

- A line starting with `k=> ` holds a form (or several, or a REPL command
  such as `:world`).
- A form continues on the following lines when they are indented by at least
  4 spaces.
- Every line after the form, up to the next `k=>` line or the end of the block,
  is the expected output. It must match what the REPL prints exactly. Trailing
  blank lines are ignored, and a form that prints nothing has no output lines.
- Output includes anything the form prints to `*out*`, before its value.
  Errors print as `!! <kind>: <message>`.
- Each markdown file runs in a fresh REPL session. The blocks of one file share
  that session, in order, so a later block can use earlier definitions.
- A block tagged `klara-repl :norun` is illustrative: it is rendered but not
  run.

To run one file from a Clojure REPL, use
`(klara.transcript-test/run-file "doc/guide/05-staging.md")`. It returns one
map per form with `:expected` and `:actual`.
