# 9. Affine regions

RFC 0005 adds optional ownership to individual values. Its first S10
milestone implements owned cells in the authority store. **The surface
syntax and static checker below are design, not runnable Klara yet.**
The implementation boundary and host API are described in
[`../background/impl/S10.md`](../background/impl/S10.md).

## Syntax (planned)

| Form | Meaning |
|---|---|
| `(own v)` | allocate a cell with full write permission |
| `(read o)` | read the persistent value of a cell |
| `(update! o f & args)` | replace its value by `(f value args..)`, requiring full permission |
| `(borrow [x o] body)` | lend read permission to `x` for this lexical scope |
| `(move o)` | transfer permission to a fresh token; invalidate the old token |
| `(freeze o)` | settle the cell and return its copyable value |
| `(drop! o)` | settle the cell without returning its value |
| `(defaffine name [params] body)` | declare a statically checked function |

Parameter hints `^:own`, `^:borrow` and `^:move` are planned under RFC
0005 §10. Ordinary values remain copyable; only explicitly owned values
are tracked.

## Meaning

An owned token uses the same authority store as evidence, budgets and
resources. A write requires its entire share, 1, with no outstanding
loans. A read requires a positive share. A borrowed token always has read
permission, including when its numerical share is 1. Returning a loan
settles that token, invalidates escaped aliases, and restores the share
to its lender. Nested loans return from the inside out.

`update!` means a functional replacement. This already runs with
persistent values and makes no promise about mutation or allocation:

```klara-repl
k=> (let [before [1 2]
          after (conj before 3)]
      [before after])
[[1 2] [1 2 3]]
```

The corresponding affine program is **design only**, because the
expander does not yet lower these names to the owned transitions:

```klara-repl :norun
k=> (let [o (own [1 2])]
      (update! o conj 3)
      (freeze o))
[1 2 3]
```

Full write permission cannot cross a fork. Read loans can: the fork
splits their fractions and settlement returns them. To allow a read-only
fork while suspending writing, lend the whole share for that lexical
scope. The store implements this rule; the lexical surface cleanup is
still to be connected to the evaluator.

```klara-repl :norun
k=> (let [o (own [42])]
      (borrow [x o]
        (fork [a (read x) b (read x)]))
      (freeze o))
[42]
```

## What remains design

The ambient `own` namespace is not admitted by core well-formedness yet.
There is no `defaffine` checker, parameter contract, derivation, or check
erasure pass. General-effect capture while a full share is held is not
restricted yet. Connecting the owned surface requires that restriction
and cleanup on normal return, exception, and abortive handler exit.

In-place JVM objects, buffers and persistent-sorted-set edit tokens,
native lowering, named lifetimes, and quantitative accounting remain
design. The successful-result contract remains value semantics: adding
ownership must preserve the observations of the functional program
(RFC 0005, AF1).
