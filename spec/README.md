# Klara specification

The normative description of the language implemented in this repository.
The [design documents](../design/00-model.md) explain *why*; this directory
states *what*, as numbered rules.

| File | Layer |
|---|---|
| [L0-core.md](L0-core.md) | Values, Core terms, evaluation, Clojure surface |
| [L1-worlds.md](L1-worlds.md) | Worlds, definitions, contexts, modules, retention |
| [L2-staging.md](L2-staging.md) | Code, links, `code` `esc` `lift` `run` `reify` |
| [L3-effects.md](L3-effects.md) | Effects, handlers, continuations, jobs, budgets |
| [L4-compiler.md](L4-compiler.md) | Preparation, checking, candidates, execution |

## Rule IDs

Every rule has an ID of the form `L<layer>.<topic>.<name>`, for example
`L2.run.closed`. The same ID appears:

- in the `:rule` key of every error or outcome the rule produces,
- in a comment at the code that implements it (`; L2.run.closed`),
- in the name or docstring of the test that checks it.

So `grep -r L2.run.closed` finds the rule, its implementation and its tests.
[rules.edn](rules.edn) lists every rule ID with a one-line summary; the test
suite checks that each listed rule is cited by at least one test.

## Conformance

`cases/` holds Klara source files with expected results. They run through the
full reader, expander, module and evaluation path. Each case states its
expected value or expected rule:

```clojure
;; expect: 27
;; expect-rule: :L2.run.closed
```

## Status

The rules describe the first version of the nucleus. Rules marked
**(planned)** are part of the design but not implemented; everything else
is implemented and tested. Proofs: none of these rules is mechanically
proved yet. The checker rules of L4 are the first targets for ansatz proofs.
