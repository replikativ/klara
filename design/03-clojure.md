# Klara and Clojure

Klara is a Clojure dialect. This is a deliberate, pragmatic choice:

1. **Existing code.** Conventional Clojure namespaces should load and run,
   within stated limits.
2. **Agents.** Models trained on Clojure should be able to write Klara without
   special prompting. Smaller models will use Klara's capabilities like tool
   calls rather than write staged generators, so every capability has a
   plain-function form.
3. **People.** Clojure programmers should recognise everything they see, and
   meet new ideas only where Klara actually differs.

## Files and namespaces

- Klara source files are `.clj` or `.cljc`. A `.cljc` file can contain
  `#?(:klara ... :clj ...)` reader conditionals; Klara reads with the
  `:klara` feature. Plain `.clj` files are read as they are.
- `(ns ...)` supports `:require` with `:as`, `:refer` and `:refer :all`, and
  `:refer-clojure :exclude`. Modules are found on the session's source roots
  (`lib/`, `src/`, `examples/` by default) by the usual path convention.
- `klara.core` is the prelude, referred automatically, with Clojure's names.
- Klara's own forms live in ordinary namespaces and must be required:
  `klara.stage` (`code`, `esc`, `lift`, `run`, `reify`), `klara.world`,
  `klara.effect` (`perform`, `handle`), `klara.job`, `klara.compiler`. A
  Clojure file that does not mention them sees no difference.
- A clj-kondo configuration shipped with Klara teaches editors these forms.

## What behaves like Clojure

- Evaluation order, truthiness, persistent collections, keywords, symbols,
  metadata-free data, `fn`/`defn` with multiple arities and variadic
  arguments, destructuring, `let`, `loop`/`recur`, `letfn`, `try`/`catch`/
  `finally`/`throw` with `ex-info`, and the convenience macros (`when`, `cond`,
  `->`, `if-let`, `doseq`, ...).
- **Late binding of globals.** Functions call the current definition of a
  name, so redefining at the REPL works as expected.
- Host functions from `clojure.core` that the prelude does not redefine are
  callable as trusted primitives, and so is Java interop for pure operations.

## What is different, and why

| Clojure | Klara | Reason |
|---|---|---|
| A var is a mutable global cell | A definition lives in an immutable world; `def` publishes a new world | Old versions remain usable, forks are cheap |
| A running loop sees every redefinition | An activation sees its own `def`s and the latest world only at `(world/advance)` | Compiled code needs a stable world |
| `println` writes immediately | `println` performs `:io/print`, whose default handler writes | Jobs can defer and discard output |
| `swap!` on any atom anywhere | Allowed outside jobs; inside a job only on atoms created in the job | Jobs are isolated |
| `binding`, `alter-var-root`, `intern`, `eval` of host forms | Not supported in the first version | They mutate the global environment behind the world's back |
| `deftype`, `defrecord`, `defprotocol`, `gen-class` | Not supported in the first version | They create host classes; they need their own world contract |
| Lazy sequences realise with whatever is current | A Klara function passed to host code runs in a nested interpreter; effects it does not handle itself are an error there (`L3.effect.host-boundary`) | The host cannot capture Klara continuations |

The list of unsupported forms is expected to shrink. Each addition needs a
statement of how it interacts with worlds and jobs, not only an
implementation.

## Two interfaces to the same capabilities

| Capability | Form-level interface | Plain-function interface |
|---|---|---|
| specialize a function | write a generator with `code`/`esc` and pass it as the recipe | `(compiler/specialize power {0 3})` |
| compile a definition | `(compiler/prepare (compiler/reference 'f) {...})` | `(compiler/optimize! 'f)` |
| try a change safely | `(job/run {:budget b} thunk)` | the same; the outcome is a map |
| look at code | `(reify f)`, `(code/view c)` | `(klara/explain f)` |
| find what keeps memory | — | `(klara/retained)` |

The plain functions are written in terms of the forms, in Klara, so they
are also examples of how to use the forms.

**Outcomes are data.** Every operation that can fail in a way the caller
should handle returns a map with `:status`. Failures carry `:rule` (a spec
rule ID), `:message` (one sentence) and, where useful, `:hint` (what to do
instead). Example:

```clojure
{:status :rejected
 :rule :L4.check.not-equivalent
 :message "candidate differs from the reference at (* x 1) vs x"
 :hint "the checker does not use algebraic identities; keep (* x 1) or add a premise"}
```

An agent can act on such a map without reading Klara's source. Errors that
indicate a programming mistake (a malformed form, an unbound name) are thrown
as `ex-info` with the same keys in `ex-data`.

## Running Klara

```sh
clojure -M:klara run examples/worlds/main.clj   # run a file
clojure -M:klara repl                            # interactive REPL
# (planned) clojure -M:klara nrepl                 # nREPL server speaking Klara
```

From Clojure (and therefore from any Clojure nREPL), `klara.host.api` offers
`(eval-string s)`, `(load-file path)` and `(session)`, so tools that already
speak Clojure can drive Klara directly.
