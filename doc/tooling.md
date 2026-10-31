# Guest source loading and nREPL

Klara can load a bounded Clojure source subset into its own worlds. This is a
trusted development interface. Explicit Clojure/Java interop remains available;
the loader and nREPL do not sandbox arbitrary host code.

## Connect to a running guest

```sh
clojure -M:nrepl --port 0 --source-root examples/compat
```

The server binds to loopback and writes its chosen port to `.nrepl-port`.
For example, using the development client:

```sh
clj-nrepl-eval --port "$(cat .nrepl-port)" '(ns scratch) (defn square [x] (* x x)) (square 7)'
clj-nrepl-eval --port "$(cat .nrepl-port)" '(load-file "examples/compat/demo/pipeline.cljc") (kernel 4) (refine) (kernel 4)'
```

The second request evaluates the reference residual, prepares and installs a
candidate, then calls it again; both kernel calls return `27`. See the
[example](../examples/compat/README.md) for the guest source.

The `eval` operation uses the Klara evaluator with no implicit host-evaluation
fallback. The optional `:host-nrepl` alias starts a conventional Clojure nREPL
instead. A useful client instruction is: evaluate guest Klara, use explicit
guest `ns` and source roots, and inspect `:repl/help` for world commands.

Supported operations are `clone`, `close`, `ls-sessions`, `describe`, `eval`
and `load-file`. Requests in a session are serialized. A clone creates a fresh
empty world, including when the request names an existing session; it is not a
world fork. Use Klara world operations for forks. Interrupt, completion and
debug middleware are not implemented. Restart the server to pick up changes
to hosted implementation code; changes to guest definitions need no JVM restart.

## Namespaces belong to worlds

```clojure
(ns demo.pipeline
  (:require [demo.polynomial :as poly]))

(defn score [x]
  (poly/evaluate poly/model x))
```

Definitions are qualified world entries. Module descriptors, including aliases
and required modules, are ordinary world data stored under `module/$module`.
Expansion records reads of these descriptors. Changing an alias can therefore
re-expand a dependent definition; forks can retain different alias mappings.
Guest definitions do not intern corresponding Clojure host Vars.

The supported `ns` slice accepts a name, optional docstring and `:require`
clauses containing `[module]` or `[module :as alias]`. Dependency lookup uses
configured source roots and prefers `.cljc` over `.clj`. The JVM reader enables
both `:klara` and its built-in `:clj` feature. Reader conditionals choose the
first matching branch: put a Klara-specific branch before `:clj`, with
`:default` last. This does not make arbitrary `.cljc` libraries compatible
with Klara.

At the REPL, top-level `(require '[module :as alias])` and `(load-file "path")`
use the guest loader. Within source files, declare dependencies in `ns`;
standalone `require`, `use`, `in-ns`, `load`, `load-file` and `eval` forms are
rejected at top level. Explicit qualified host interop remains possible.
`:refer`, `:rename`, `:import`, `:gen-class`, reload flags, cyclic dependencies
and full Clojure namespace reflection are unsupported. Required modules are
cached by descriptor presence; explicit `load-file` reloads the named file.

Loading stages definitions and dependencies in a temporary world and publishes
one root. A failure leaves the target definitions unchanged. A concurrent
publication causes a conflict rather than replaying the whole file. External
host effects performed during reading/expansion/initialization are not rolled
back. Ordinary definition publication can retry initializers on conflicts.

Optional baseline preparation runs after successful file publication. The host
API shares one explicit job across files:

```clojure
(require '[klara.compile.prepare :as prep]
         '[klara.load :as load] '[klara.stage :as stage] '[klara.world :as world])
(def w (world/make-world))
(def cache (stage/make-cache))
(def job (prep/job))
(def options {:prepare :baseline :cache cache :preparation-job job})
(load/load-string! w "(def square (fn [x] (* x x)))" options)
;; The return map includes a separate :preparation report.
```

`repl/session` accepts `{:prepare :baseline}` and shares a job across its file
loads. For the guest nREPL server, add `--prepare baseline`; `--prepare off` is
the default. Standalone interactive `def` keeps its existing behavior. Preparation
decline/exhaustion leaves a successfully loaded program available to T0. This
can prepare functions before their first application call, but cannot accelerate
initializers that loading has already executed. See the
[implementation limits](engineering/compiler.md#consolidated-implementation-boundaries).

The [compiler-service example](../examples/compat/klara/compiler.cljc) can be
loaded with `(require '[klara.compiler])` from `examples/compat`. It generates
a transfer producer with `code/esc`, installs a world-defined selection policy,
and exposes `prepare-code` for ordinary staged preparation. The
[architecture walkthrough](engineering/compiler.md) shows the complete guest
REPL sequence and explains why edited compiler services remain stepped.
The [residual walker module](../examples/compat/klara/residual.cljc) adds bounded
inspection/rebuilding of existing Code; see the [Code-view walkthrough](engineering/code-views.md).

The Clojure reader still uses temporary host namespace scaffolding and alias
target namespaces. Guest bindings are not host Vars, but this is not yet a
complete host-independent reader or a complete definition-site module hygiene
model. Syntax extensions should emit explicit qualified guest globals, as the
example does. Module descriptors are not sealed abstract identities from
RFC 0007.

## Mutable state and effects

Persistent definition roots do not recursively snapshot host objects. An atom
created through `clojure.core/atom` remains shared across world forks. Known
host writes can be deferred by authority forks; this does not give them
branch-local atom semantics. Managed references remain a separate design task.

Host calls and Var/static access have explicit Core effect operations, but
their default handlers can execute arbitrary host behavior. The boundary is
not a complete effect analysis: mutable reads, writes and state reached
through callbacks need contracts before isolation or optimization across them
can be justified. Unsupported host behavior has no general JIT-safety or
speculation guarantee. See the [interop guide](guide/07-clojure-interop.md).

## Checks

```sh
clojure -M:test
clojure -M:test-nrepl
```

The optional protocol test opens a loopback socket. It checks guest evaluation,
session persistence/separation, source loading and error reporting. The
ordinary tests cover alias changes across forks, old-world closures, macro
invalidation and failed loads. These are implementation tests, not a proof of
the entire loader, macro system or host boundary.
