# Guest modules, syntax and specialization

The [local optimizer module](klara/local_optimizer.cljc) is a separate staged
compiler example: its guest use analysis proposes local-call inlining, a host
checker applies the fixed recipe, and the same preparation operation works
before use or later in an authority fork. See the
[walkthrough](../../doc/engineering/guest-local-calls.md) for runnable code and
the limits of the implemented composition contract.

This fixture loads two guest `.cljc` modules and connects ordinary functions,
a syntax extension and staged compilation. Start the
[guest nREPL](../../doc/tooling.md) with `examples/compat` as a source root, then:

```clojure
(load-file "examples/compat/demo/pipeline.cljc")
(score 4)
;; => 27
(kernel 4)
;; => 27
(refine)
;; => {:status :installed, ...}
(kernel 4)
;; => 27
```

[`demo.polynomial`](demo/polynomial.cljc) defines immutable coefficients and a
recursive reference evaluator. [`demo.pipeline`](demo/pipeline.cljc) imports
it through an alias. Its `polynomial` syntax extension invokes a guest code
builder that embeds the coefficients into a unary function. The generated
expression preserves the reference's addition/multiplication order, including
its terminal zero; this example does not assume unrestricted algebraic laws
for floating-point arithmetic.

`refine` prepares the code inside an authority fork, adopts the candidate and
requests installation after fork exit. This uses the existing staged compiler
admission path. It does not prove arbitrary syntax extensions correct or
establish a speedup for this small polynomial.

Definitions and aliases live in Klara worlds. Tests change the coefficient
definition and verify that dependent generated code is refreshed while a
previously retained kernel keeps its old-world result. Separate tests change
an alias in a child world and verify parent/child separation.

The fixture requires only the bounded namespace/loader subset described in
the tooling guide. It is not evidence that an arbitrary Clojure library loads.

[`klara.compiler`](klara/compiler.cljc) is a second guest example: staging
specializes the transfer-plan producer by arity, and an ordinary world policy
selects the generated service during compilation. Its `prepare-code` helper
uses the existing preparation fork and installation protocol for closed Code.
See the [architecture walkthrough](../../doc/engineering/compiler.md) for the
REPL sequence, compiler-service budget boundary and rejection cases.

[`klara.residual`](klara/residual.cljc) uses the bounded Code view to implement
generic identity regeneration and literal-branch pruning. It preserves binders
through opaque cursors and never evaluates arithmetic during rewriting. The
[walkthrough](../../doc/engineering/code-views.md) distinguishes scope safety,
unchanged source identity and semantic replacement of an existing entry.
