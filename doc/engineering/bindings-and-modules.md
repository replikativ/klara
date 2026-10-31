# Binding, modules and staging

This document separates the current hosted implementation from the language
contract still to be formalized. Lexical hygiene alone does not specify module
resolution or cross-stage binding. These distinctions matter both for ordinary
loading and for optimizers that construct Code.

## Current implementation

There are three different uses of names:

| Representation | Meaning |
|---|---|
| Surface identifier | Resolved by the expander using lexical scopes, module context and the pinned world |
| Core `:resolve` | A world definition identified by its global symbol; evaluation uses the applicable world basis |
| Core `:prim` | An intrinsic operation selected during expansion; its symbol is an opcode, not a new identifier lookup |

For example, an ordinary call to `+` can resolve to a lexical or world
definition before the primitive fallback is considered. Once expansion has
produced a primitive addition node, a later local binding named `+` cannot
change that node's meaning. Likewise, map literal syntax selects the intrinsic
`literal-map`; an ordinary function call named `literal-map` remains subject to
name resolution. This distinction needs to survive all backend lowerings.

The current expander has built-in forms and a primitive fallback table. It also
falls back to host Clojure macros and functions. This is a compatibility policy,
not a fully specified `clojure.core` import declaration. Call-head resolution
and value-position resolution have different implementation paths; they should
not be summarized as a universal Clojure namespace lookup rule.

The loader supports a bounded `ns`/`require` subset with explicit aliases.
Module descriptors and definitions are stored in the world, and definitions
retain module context for re-expansion. Its temporary Clojure reader namespace
refers to `clojure.core` for reading, including syntax-quote naming. Reading,
guest binding resolution and host namespace loading are distinct operations.
The reader adapter is not a complete specification of module hygiene.

The JVM backend maps primitive opcodes to qualified host implementations.
Generated forms are evaluated under a controlled backend namespace, rather
than the caller's host namespace. This prevents ordinary caller aliases or
missing core refers from changing emission. Host Vars remain mutable trusted
host state: qualification alone neither freezes their roots nor proves purity.
Existing guards and effect boundaries must still account for that state.

Code inspection and template composition preserve lexical scope through
binding identities and freshening. That does not by itself establish
definition-site module binding, phase separation, or semantic equivalence of
a replacement. See [Code views](code-views.md).

## Current staging support and an open world-binding contract

The expander and CEK already track staging levels for `code`/`esc`, generated
lexical binders and scope-extrusion checks. CodeVar markers carry a level during
construction. Global definitions, however, are keyed by symbol in a world root;
there is no general phase-indexed global environment. Code values currently
contain syntax, not an explicit global home-stage or captured reference root.

Definition dependency recording already distinguishes residual references from
values consumed while generating code:

```clojure
(def setting 10)
(def late (code (+ setting 1)))
(def frozen (let [value setting] (code (+ value 1))))
```

After redefining `setting` as 20, `late` still denotes Code with a global lookup:
it produces 21 under the new root and 11 under the old root. `frozen` consumed
`setting` while generating Code, so its definition becomes pending under the
changed value generation. Its previously saved Code still produces 11. This is
partial stage-sensitive dependency handling, not complete phase-aware `def`/Var
semantics.

**Implemented safety boundary:** lifting rejects a pinned closure whose body
contains world resolutions, including a pinned dependency reached through
captured closures, collections or partial applications. The recursive fallback
checks this too. A pin alone is not unsafe: world-independent functions and
ordinary data still lift. This is deliberately conservative (including staged
references), pending a contextual linking representation. Open closure behavior
and explicit late-bound Code retain their existing semantics.

The former diagnostic showed an old pinned reader returning 10 while its lifted
body read 20 in a new world. That crossing now rejects rather than silently
relocates. Historical observations remain in
[the original report](../../experiments/consolidation/stage-world-bindings-results.edn);
this is not a universal `run(lift(v)) = v` theorem. Pure host functions remain
opaque constants, not an effect sandbox. General phase-aware global identities,
explicit relocation and preservation of arbitrary global contexts remain open.

The direction to discuss is an explicit, persistent staging/binding environment:
binding identities, phase availability and cross-stage/world linking policy
should be inspectable with the code. A single absolute integer on every stored
program is insufficient: quoted code can later execute, and the same helper may
be usable at several stages under an explicit persistence contract. Stage context
and world/definition generation remain distinct coordinates, even when both are
represented in the same persistent memory graph. See the
[codebase map](codebase-map.md) for the current/proposed lifecycle separation.

## Proposed semantic boundary

Keep Clojure-compatible surface conventions where useful, but describe lookup
explicitly. A useful model is a judgment of the form:

```text
resolve(world, module, phase, lexical-scopes, identifier) = binding
```

Bindings should distinguish lexical identities, module exports, intrinsic
operations and explicit host capabilities. A module binding's identity should
be separate from the value or definition version selected in a world. Forking
can then preserve binding identity while choosing different definitions.
Whether a compiled artifact pins a version, performs a world lookup, or guards
a version assumption must be recorded separately.

The first specification should define:

1. Which core bindings are implicitly imported, how imports can be excluded or
   renamed, and which forms are reserved syntax. An explicit prelude can give
   the convenient default without making imports an ambient host assumption.
2. How aliases, exports, missing bindings, cyclic loading and failed loading
   behave. Atomic publication of a loaded module is a design question, not a
   consequence of having persistent roots.
3. Which definition-site bindings introduced syntax retains, and which
   use-site bindings spliced syntax retains. Printed symbol equality is
   insufficient for either rule.
4. How expansion-time transformer bindings relate to runtime bindings.
   Expansion phase and staging level should be modeled separately: a macro
   expansion and a runtime specialization are not the same event merely
   because both construct code.
5. What `code`, `esc` and `run` preserve across stages: lexical scope,
   module references, world assumptions and permitted effects. Closedness in
   local variables does not imply independence from global definitions.

For compiler caching, expansion dependencies must include the module/import
and transformer facts actually used. An import or transformer change can
require re-expansion even when runtime callees are unchanged. Such dependencies
remain distinct from runtime guards and from compiler provenance that does not
affect the validity of an independently checked result.

For example, a transformer that introduces a helper should retain its intended
definition-site binding even if its caller defines the same printed name. A
user expression spliced into that expansion should retain the user's binding.
A staged optimizer that moves either expression must preserve these identities
and justify effects, evaluation order and any changed world assumptions.

## Consolidation order

First specify and test the existing resolution paths, including intentional
differences from Clojure. Then make the prelude and module binding contract
explicit before broadening loading or adding more implicit host fallbacks.
Only then generalize language extensions around persistent transformer and
module environments. Racket-style scopes and phase separation are useful
design references; full Racket compatibility is not an implementation claim.

The focused correctness obligations are resolution determinism under a pinned
environment, preservation of binding by expansion and Code construction,
non-capture under composition, and invalidation when a recorded binding fact
changes. Rejection tests should include helper-name capture, alias changes
between worlds, unsupported phase crossings, and code whose free module
bindings are unavailable at its destination. Existing lexical scope tests
cover only part of this boundary.
