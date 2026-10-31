# L1 Worlds

## Worlds and definitions

`L1.world.value` A world is an immutable value with an identity `:id`, a
`:parent` id, and a map from qualified symbols to definitions. Two worlds
with the same id are the same world.

`L1.world.definition` A definition records `:name`, `:form` (source),
`:term` (Core), `:value`, `:generation` and `:reads` (the globals its
initializer term mentions). Generations are unique: no two evaluations of
any definition share one.

`L1.world.define` `(world/define w name value)` returns a new world equal
to `w` except that `name` is defined as `value`. It does not change the
session; `(world/publish! w)` does (`L1.session.publish`).

`L1.session.conflict` Publishing a change to a name whose definition was
changed by another publication since the change was made raises this
rule. Worlds record only the base entries of the names they change
(their *delta*), not their base world.

## Sessions and activations

`L1.session.current` A session holds its current world in a single cell.

`L1.session.publish` Publishing world `w2` derived from `w1` succeeds if the
session's current world is still `w1`. If another publication intervened,
the change is merged when the two changed disjoint sets of names, and fails
with `L1.session.conflict` otherwise.

`L1.context.top` A top-level activation starts with effective world `E` =
the session's current world and mint `m` = `nil`.

`L1.context.resolve` A global with a late link resolves in `E`.
A name not defined there raises `L1.resolve.unbound`.

`L1.context.mint` A closure created while the context has mint `m` has
basis `m`.

`L1.context.call-open` Calling a closure with no basis leaves `E` and `m`
unchanged.

`L1.context.call-based` Calling a closure with basis `w` evaluates its body
with `E = m = w`, and restores the caller's context on return.

`L1.context.in` `(world/in w f & args)` calls `f` with `E = m = w`.

`L1.context.get` `(world/get w 'q)` returns the value of `q` in `w`. If the
value is a closure without basis, it is returned with basis `w` (a slice of
`w`, `L1.slice.*`).

`L1.def.effect` `(def q e)` evaluates `e` with `m = nil` and then performs
`:world/define`. The session's default handler publishes the new world and
sets the activation's `E` to it (`L1.def.read-your-writes`). In a pinned
context (`m` not nil) `def` raises `L1.def.pinned`.

`L1.def.pinned` `def` in a pinned context (mint not nil) raises this rule:
a pinned world is a fixed past, not a place to define.

`L1.context.advance` `(world/advance)` sets `E` to the session's current
world. It is an error in a pinned context.

`L1.context.current` `(world/current)` returns `E`.

## Modules

`L1.module.ns` `(ns name ...)` sets the current namespace, records its
aliases and refers, and refers `klara.core`.

`L1.module.require` `(:require [a.b :as x :refer [f]])` loads `a/b.clj`
or `a/b.cljc` from the session's source roots if `a.b` is not yet defined
in the current world, then records the alias and refers. `klara.*`
namespaces provided by the runtime are not loaded from files.

`L1.module.load` Loading a file evaluates its forms in order, each as an
activation, so later forms see earlier definitions.

## Slices and footprints

`L1.slice.footprint` The footprint of a definition is the smallest set of
names containing the globals of its term and of every closure reachable
from its value, closed under the same rule in the world.

`L1.slice.resolve` A slice of `w` to footprint `F` resolves every name in
`F` as `w` does. Resolving a name outside `F` is an internal error
(`L1.slice.missing`), never a silent fallback.

`L1.slice.missing` Resolving a name outside a slice's footprint raises this
rule. It indicates an unsound footprint, an implementation error.

`L1.slice.dynamic` If a footprint contains `run`, `world/current`,
`world/advance`, `eval` or `world/get` with a non-constant name, the slice is
the whole world.

## Retention

`L1.retain.roots` Klara memory is reachable only from the roots listed in
[design/01-lifetimes.md](../design/01-lifetimes.md#roots).

`L1.retain.history` A world refers to its parent by id only. The session's
history log holds summaries `{:id :parent :changed}` and keeps at most
`:history-limit` of them (default 1000).
