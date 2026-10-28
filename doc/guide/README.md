# The Klara guide

<!-- The guide agent owns this file except for the section "Transcripts"
     below, which documents the format checked by test/klara/transcript_test.clj. -->

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
