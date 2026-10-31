# L0 Core

## Values

`L0.value.data` Values include Clojure's immutable data: `nil`, booleans,
numbers, strings, characters, keywords, symbols, and persistent lists,
vectors, maps and sets of values.

`L0.value.fn` A *function* is a Klara closure: arities, captured locals,
an optional basis world (L1) and an optional name. Host functions
(`clojure.core/+`) are also values; they are called directly.

`L0.value.other` Worlds, Code, continuations and candidates (L1 to L4) are
values. They are immutable. Host objects that are not immutable (atoms,
arrays) may be values but are *mutable* for the purposes of L2 and L3.

## Core terms

The expander translates source forms to Core terms, which are maps with an
`:op`. Locals have unique names after expansion.

| `:op` | Fields | Meaning |
|---|---|---|
| `:const` | `:value` | the value |
| `:local` | `:name` | a local variable |
| `:global` | `:link` | a world definition, through a link (L2) |
| `:host` | `:name` | a trusted host function, by qualified symbol |
| `:fn` | `:self` `:arities` `:free` | a closure; each arity has `:params`, `:rest`, `:body` |
| `:app` | `:fn` `:args` | call |
| `:let` | `:name` `:init` `:body` | bind one local |
| `:letrec` | `:bindings` `:body` | mutually recursive local functions |
| `:loop` / `:recur` | `:bindings` `:body` / `:args` | Clojure `loop`/`recur` |
| `:if` | `:test` `:then` `:else` | branch on truthiness |
| `:do` | `:body` | sequence; value of the last |
| `:throw`, `:try` | `:ex` / `:body` `:catches` `:finally` | exceptions |
| `:interop` | `:target` `:member` `:args` `:static?` | trusted host method or field access |
| `:def` | `:name` `:init` `:form` | define a global (L1) |
| `:perform`, `:handle` | | effects (L3) |
| `:code`, `:esc` | `:body` | staging (L2) |

`L0.term.wf` A term is well formed if its locals are bound, `:recur` occurs
only in tail position of `:loop` or an arity body with the same number of
arguments, and `:esc` occurs only inside `:code`. Expansion produces only
well-formed terms; violations are reported with the rule of the offending
construct.

`L0.term.free` Every `:fn` term records `:free`, the locals its body
mentions that are bound outside it.

## Evaluation

The reference semantics is a CEK machine (`src/klara/runtime/machine.clj`):
a state is a control (a term to evaluate or a value to return), an
environment and a continuation, a list of frames that are plain data.

`L0.eval.order` Subterms are evaluated left to right. In a call the function
position is evaluated first, then the arguments.

`L0.eval.truth` `nil` and `false` are false; every other value is true.

`L0.eval.call` Calling a closure selects the arity matching the number of
arguments (or the variadic arity), binds parameters, and evaluates the body
in the captured environment plus the parameters. No matching arity raises
an `ArityException`-equivalent `ex-info` with rule `L0.eval.arity`.

`L0.eval.host` Calling a host function applies it to the argument values.
A host exception becomes a Klara exception at that point.

`L0.eval.tail` A call in tail position pushes no frame (proper tail calls).
`recur` reuses the current loop or arity without growing the continuation.

`L0.eval.exception` `throw` raises its value (which must be a `Throwable`).
`try` catches by class, in order, and runs `finally` on every exit,
including when the exception is not caught and when a continuation exits
through it. A continuation that *re-enters* a `try` body does not re-run
anything already run.

`L0.space.closure` A closure captures exactly its `:free` locals.

`L0.space.tail` A loop expressed with tail calls or `recur` runs in bounded
continuation size.

## Surface

`L0.surface.read` Source is read by the Clojure reader with reader
conditionals enabled for the feature `:klara`. `*read-eval*` is false.

`L0.surface.special` The special forms are `def`, `if`, `do`, `let*`,
`loop*`, `recur`, `fn*`, `letfn*`, `quote`, `throw`, `try`, `.`, `new`, plus
`klara.stage/code`, `klara.stage/esc`, `klara.effect/handle`. Clojure's macros
(`defn`, `let`, `when`, `cond`, `->`, ...) are expanded by their host
definitions, and their expansions are expanded again.

`L0.surface.resolve` A symbol in operator or value position resolves, in
order, to: a local; a definition in the current namespace, then a referred
or aliased definition; a host function of `clojure.core` that is in the
trusted table; a host class. Otherwise expansion fails with
`L1.resolve.unbound`.

`L0.surface.unsupported` `binding`, `set!`, `var`, `alter-var-root`,
`intern`, `eval`, `deftype`, `defrecord`, `defprotocol`, `reify` (the
Clojure form), `gen-class`, `case*` and `monitor-enter` are rejected with
this rule. Klara's `case` is a macro over `=`.
