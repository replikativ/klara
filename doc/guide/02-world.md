# 2. Definitions, the world, bases

A Clojure program lives in namespaces of mutable vars. A Klara program lives
in a **world**: an immutable, versioned map from names to definitions. A
definition does not overwrite anything; it publishes a new root of the world.
Code always runs against one root, its **basis**. This chapter shows what a
definition records, what happens when you redefine something at the REPL,
and the *pending* state that protects running code from stale expansions.

## Definitions

`def`, `defn`, `defsyntax` and `defmacro` publish a definition. The REPL prints the name.

```clojure klara-repl
k=> (defn sq [x] (* x x))
#'sq
k=> (def three 3)
#'three
k=> (sq three)
9
k=> (perform :world/version)
2
```

Each definition goes through one pipeline (`klara.defs/define!`):

1. **expand** the form against the current root, recording every read of
   the world;
2. compute the **CodeId** of the expanded core term (chapter 1);
3. **evaluate** the term in T0 under that root;
4. **publish** the entry with a single compare-and-set on the world
   reference. If another publication won the race and the recorded reads
   still hold in the new root, the work is rebased instead of redone.

An entry holds the source form, the core term, the CodeId, the value, the
recorded reads and a version history. `(perform :world/version)` is the
version of the root the code runs under: each publication increments it.

## Recorded reads

The expander and the definition-time evaluator read the world only through
a recording lookup. There are four kinds of read:

| Read | Recorded when | Broken when |
|---|---|---|
| `[:def s]` | code refers to the definition `s` (a late-bound call) | `s` stops being a non-macro definition |
| `[:macro s h]` | expansion ran macro `s` with transformer `h` | the macro's transformer changes |
| `[:value s h]` | evaluation at definition time consumed `s`'s value | `s`'s value changes |
| `[:absent s]` | the expander looked for `s` and did not find it (a **negative lookup**) | `s` gets defined |

A *runtime* reference is late bound: redefining a function does not touch
its callers, which simply call the new version next time they resolve it.

```clojure klara-repl
k=> (defn helper [x] (+ x 1))
#'helper
k=> (defn caller [x] (* 2 (helper x)))
#'caller
k=> (caller 5)
12
k=> (defn helper [x] (+ x 100))
#'helper
k=> (caller 5)
210
```

The REPL printed nothing besides the name: no dependent needed work.

## Redefining a macro

A macro is a world definition too: a transformer closure run by T0 at
expansion time. Code that used the macro holds an expansion of the old
version, so redefining it makes that code stale. The REPL repairs the
dependents at once and reports what it did.

```clojure klara-repl
k=> (defsyntax twice [[e :expr]] (qq (+ ~e ~e)))
#'twice
k=> (defn f [y] (twice y))
#'f
k=> (f 3)
6
k=> (defsyntax twice [[e :expr]] (qq (* ~e ~e)))
#'twice
;; stale: f
k=> (f 3)
9
```

`;; stale: f` means `f` was re-expanded and re-evaluated. (`qq` is Klara's
quasiquote: unlike Clojure's syntax-quote it does not namespace-qualify
symbols; hygiene comes from scope sets instead.)

If a change to the macro does not change what it produces, the dependent is
re-expanded, its CodeId compared, and nothing else happens. This is the
**early cutoff**:

```clojure klara-repl
k=> (defsyntax twice [[x :expr]] (list '* x x))
#'twice
;; cutoff: f
k=> (f 3)
9
```

Values computed at definition time are tracked in the same way:

```clojure klara-repl
k=> (def base 2)
#'base
k=> (def derived (* 10 base))
#'derived
k=> (def base 5)
#'base
;; stale: derived
k=> derived
50
```

And so are names that were *not* there. `g` below calls clojure.core's
`inc`, because the world did not define `inc` when `g` was expanded. That
absence was recorded; defining `inc` in the world re-expands `g`:

```clojure klara-repl
k=> (defn g [x] (inc x))
#'g
k=> (g 1)
2
k=> (defn inc [x] (+ x 100))
#'inc
;; stale: g
k=> (g 1)
101
```

## The pending state

The REPL is a convenience layer: after every definition it runs
`klara.defs/invalidate!`, which re-checks all dependents and publishes the
repairs in one more compare-and-set. Underneath, publication and repair
are separate steps, and in between a dependent whose reads broke is
**pending**: resolving it is an error, never a silent run of the old
expansion.

A world fork (chapter 4) does not auto-repair, so it shows the state.
`(perform :world/fork)` makes a snapshot of the current world;
`(perform :world/eval-in w form)` defines or evaluates a quoted form in it.

```clojure klara-repl
k=> (defsyntax twice [[e :expr]] (qq (+ ~e ~e)))
#'twice
;; stale: f
k=> (def w (perform :world/fork))
#'w
k=> (perform :world/eval-in w '(defsyntax twice [[e :expr]] (qq (- ~e 1))))
twice
k=> (perform :world/eval-in w '(f 3))
!! pending: f is pending re-expansion in this basis
k=> (perform :world/invalidate w 'twice)
{:stale [f], :green [], :cutoff [], :reexpanded [f]}
k=> (perform :world/eval-in w '(f 3))
2
k=> (f 3)
6
```

`invalidate` reports each dependent as *green* (all reads still hold),
*cutoff* (re-expanded to the same CodeId; value kept) or *stale*
(re-expanded and re-evaluated). The session's own `f` is untouched: the
fork's edit is invisible outside the fork.

## Syntax values and grammars (S13)

`defsyntax` is a world transformer run by T0, like `defmacro`, with a grammar
instead of an argument list. Its captures are **syntax values**: datum,
scope sets, source location and a property map. Copy captures into output to
preserve their binding context. Existing `defmacro` definitions still receive
raw reader data; use them for compatibility with data-oriented macros.

```clojure klara-repl
k=> (syntax? (quote-syntax (+ x 1)))
true
k=> (syntax->datum (quote-syntax (+ x 1)))
(+ x 1)
k=> (syntax-property (syntax-property (quote-syntax x) :role :input) :role)
:input
k=> (defsyntax scoped [[b :binding] [e :expr] [body :body ...]]
      (list* 'let* [b e] body))
#'scoped
k=> (scoped x 3 (+ x 2))
5
k=> (defsyntax surround [[e :expr]] (qq (let* [tmp 100] ~e)))
#'surround
k=> (let [tmp 7] (surround (surround tmp)))
7
```

`quote-syntax` retains lexical scopes; `quote` removes them. `syntax-e`
exposes one datum layer, while `syntax->datum` recursively removes syntax
wrappers and metadata. `datum->syntax` gives new datum the scopes and source
of a context syntax value, preserving embedded syntax values. It is an
explicit way to introduce a binding in a caller's context. `syntax-property`
reads a property with two arguments and returns an updated value with three.
Syntax values and staged code values (chapter 5) are separate types.

The grammar is a vector of argument patterns. Nested lists/vectors match
structure; non-capture atoms are datum literals (symbols compare by spelling).

| Pattern | Capture |
|---|---|
| `[e :expr]` | an expression, locally expanded once and safe to splice under binders |
| `[b :binding]`, `[b :id]` | an identifier |
| `[body :body]` | unexpanded syntax, for a body whose bindings are introduced later |
| `[body :body ...]` | zero or more items, captured as a vector |
| `(:optional pattern)` | zero or one match; absent attributes are `nil` |
| `(:repeat pattern)` | zero or more structured matches; each attribute is a vector |
| `[p :pair]` | a reusable world-defined class named `pair` |

Optional/repeated patterns are greedy, backtracking to match the suffix.
Parsing may try an expression on more than one branch: transformers should
be pure. Duplicate pattern variables are rejected. There are no grammar
alternatives, literal-binding comparisons or ellipsis-depth attributes yet.

```clojure klara-repl
k=> (defsyntax-class pair [[left :expr] [right :expr]])
#'pair
k=> (defsyntax add-pair [[p :pair]]
      (qq (+ ~(syntax-attribute p 'left) ~(syntax-attribute p 'right))))
#'add-pair
k=> (let [x 3] (add-pair [x 4]))
7
k=> (defsyntax unless [[test :expr] [body :body ...]]
      (qq (if ~test nil (do ~@body))))
#'unless
k=> (unless false 1 (+ 2 3))
5
```

A class is an ordinary world function returning an attribute map. Its grammar
matches the captured value's datum sequence. `syntax-attribute` retrieves an
attribute from the enclosing capture. Reading the class is a recorded world
value read, so changing it invalidates dependent expansions just like a
transformer or schema edit. Pattern failures carry `:source`, `:path` and
`:expected` in their exception data and print the available file/line/column.
Reader positions are retained where available; an atom without its own span
uses the enclosing form's location.

## Local expansion and private syntax definitions

Within a transformer, `(local-expand syntax)` expands in the active lexical
environment and basis. The returned syntax retains named lexical references:
splicing it under a new binder cannot capture them, and using it after its
binder has disappeared fails. Every lookup, including absence and values
read by nested transformers, enters the enclosing definition's read set.
The macro memo validates and replays those reads; removing it gives the same
canonical core and CodeId. Host state reads remain outside these guarantees.

`definition-context` creates an isolated lexical transformer namespace.
`bind-syntax!` registers an identifier and a T0 transformer accepting syntax
arguments. Pass the context as the second argument to `local-expand` to
activate it. Private bindings inherit outer definition contexts, keep their
scope when they introduce calls, and do not become world definitions.

```clojure klara-repl
k=> (defsyntax locally [[body :body]]
      (let [dc (definition-context)]
        (bind-syntax! dc (quote-syntax private) (fn [v] (qq (+ ~v 10))))
        (local-expand body dc)))
#'locally
k=> (let [x 5] (locally (private x)))
15
k=> (private 5)
!! expand: unable to resolve private
```

A definition context is valid only during its creating transformer invocation;
using a saved context in a later invocation fails. This first interface expands
expressions fully: it has no stop list, module phases, definition lifting or
recursive variable-definition contexts. These are explicit future extensions,
not changes to T0 meaning. See RFC 0006 LG1/LG2 and the
[runtime contracts](../engineering/runtime.md) for the tested scope
of the guarantees.

## Bases

Code runs against a basis, and three rules decide which:

1. A **top-level evaluation** at the REPL runs against the newest root of
   the current world.
2. A **closure** created while code runs keeps the basis it was created
   under. A closure is a value; a later definition does not reach into it.
3. A **world definition** is stored as an *open* closure and runs under the
   basis of whoever resolves it. This is why one definition value works in
   several forks, each seeing its own versions of the names it calls
   (example 8, `examples/klara/08-coupled-fork.md`).

A **fiber** pins a basis and keeps it until it performs
`(perform :world/raise-basis)`; `(perform :world/resolve 'name)` looks a
name up in the fiber's current pin. Example 9
(`examples/klara/09-basis-raise.md`) runs a simulation in a fiber while
the REPL redefines its step function.

**Meaning.** The spec models the world as a finite map read by `resolve`
(rule `resolve`, named stuck state `unbound`). Versions, bases, open
closures and the pending check are T0's extension (`doc/semantics.md` §9).
The guarantees are tested rather than proved: gate R4 (old and new
versions coexist across forks and pinned fibers, concurrently, in
`test/klara/r4_test.clj`) and the X1 criteria (`x1_test.clj`).

## Not yet implemented

- A lost compare-and-set race re-evaluates the definition, repeating any
  definition-time effects.
- The pending check costs time proportional to the entry's reads on every
  resolve.
- Expansion results are memoized for one session only; there is no
  content-addressed cache shared across forks.
- clojure.core macros are host reads and are not recorded.
