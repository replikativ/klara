# 9. Affine regions

Ownership is optional per value. Owned cells extend the authority store
used by evidence, budgets and forks. T0 checks every use; a small static
fragment can move those checks to compilation (RFC 0005).

| Form | Meaning |
|---|---|
| `(own v)` | allocate a cell with full write permission |
| `(read o)` | read its persistent value |
| `(update! o f & args)` | replace its value by `(f value args..)`, returning o |
| `(borrow [x o] body..)` | lend the whole available share as read permission for a lexical scope |
| `(move o)` | return a fresh token, invalidating the old token |
| `(freeze o)` | settle the cell and return its copyable value |
| `(drop! o)` | settle the cell, returning nil |
| `(defaffine name [params] body..)` | declare a function in the checked fragment |

These names can be shadowed by local or world definitions. Ordinary
values remain copyable. There is no implicit drop at last use: settle
owned cells explicitly. The context-chain check conservatively includes
live full shares even when a local no longer refers to them.

## Functional meaning

A write requires the entire share, 1, with no outstanding loans. Reading
returns a persistent snapshot: subsequent updates leave earlier values
intact. Updates call f once and publish its result only on success.
Callbacks must be functional; arbitrary host mutation is outside this
value-semantics contract.

```clojure klara-repl
k=> (let [before [1 2] o (own before) snapshot (read o)]
      (update! o conj 3 4)
      [before snapshot (freeze o)])
[[1 2] [1 2] [1 2 3 4]]
k=> (let [o (own 7) next (move o)] (freeze next))
7
k=> (let [o (own 0)] (freeze o) (freeze o))
!! authority: freeze: authority is settled (freeze)
```

## Lexical read loans and forks

A borrowed token always has read permission, even when its share is 1.
The lender cannot be used while the whole share is lent. Nested borrows
are allowed. Normal return, exception and handler exit close the loan,
invalidate escaped aliases and restore the lender's share.

Read loans can cross forks: the existing authority machinery splits and
recombines their fractions. Full write permission cannot cross a fork.

```clojure klara-repl
k=> (let [o (own [42])]
      (let [values (borrow [x o] (fork [a (read x) b (read x)]))]
        [values (freeze o)]))
[[[42] [42]] [42]]
k=> (let [o (own 0)]
      (try (borrow [x o] (update! x inc))
           (catch Exception e (drop! o) :rejected)))
:rejected
k=> (let [o (own 0)]
      (try (fork [a 1 b 2])
           (catch Exception e (drop! o) :rejected)))
:rejected
```

T0 checks operation classes before capture. A Klara handler clause may
ignore its continuation, or use it only as a direct final call through
lets/ifs. Other clauses, including unknown host clauses, cannot capture
while the context holds a full share. A declaration alone is never
trusted. This is a conservative decision procedure: some more complex
but semantically tail-resumptive clauses will be rejected.

```clojure klara-repl
k=> (let [o (own 0)]
      (try (handle [h {:ask (fn [k] (+ 1 (k 2)))}] (perform h :ask))
           (catch Exception e (drop! o) :rejected)))
:rejected
```

## Parameter contracts

Function parameters accept `^:own` (check full write permission),
`^:borrow` (a read loan returned at function exit) and `^:move` (consume
the caller's token and bind a fresh callee token). These are runtime
contracts on ordinary functions; conflicting hints are rejected.

```clojure klara-repl
k=> (defn view [^:borrow x] (read x))
#'view
k=> (let [o (own [3])] [(view o) (freeze o)])
[[3] [3]]
k=> (defn take-value [^:move x] (freeze x))
#'take-value
k=> (let [o (own 9)] (take-value o))
9
```

## Static checking and compilation

`defaffine`, or `def` with a `^:affine` name, checks before publication.
`klara.affine/check` accepts a core term and returns an EDN derivation.
Its `:declared` mode rejects with a path and diagnostic; its default
`:inferred` mode returns the same facts on success and nil on failure.

The first fragment supports local allocations, pure callbacks, reads,
moves, settlement, lexical loans, matching ownership at branch joins and
single recursive loops whose back edges preserve ownership. Every owned
place must be frozen or dropped; owned tokens and loans cannot escape.
Unknown calls, effects and owned parameter contracts stay outside this
static fragment. Ordinary T0 code can use all the dynamic features above.
Erased entry checks admit closed immutable host data; opaque objects and
custom collection protocols fall back to T0 before effects.

```clojure klara-repl
k=> (defaffine counter [n]
      (let [o (own [0])]
        (loop [i 0]
          (if (< i n)
            (do (update! o (fn [v] (assoc v 0 (inc (nth v 0)))))
                (recur (inc i)))
            nil))
        (freeze o)))
#'counter
k=> (counter 4)
[4]
k=> :repl/compile counter
;; compiled counter: affine-erase -> affine-represent -> emit
;; guards 3; allocations removed 0
k=> (counter 1000)
[1000]
```

`klara.compile.affine-erase/erase` rechecks the derivation before removing
checks. Most cells hold persistent values in private boxes. Literal Long
vectors with only the exact increment-at-index callback above can use a
private `long[]`; reads/freeze still produce persistent snapshots. The
allocation experiment in `experiments/affine/bench.clj` measures a flat
allocation slope from 1,000 to 1,000,000 iterations. Entry and result
allocations remain. This is finite testing, not a soundness proof.

## What remains design

Broader static inference, erasure of owned argument contracts, general
effects inside static islands, named lifetimes, arbitrary vector/array
updates in place, persistent collection edit tokens, JS/native lowering
and kernel proofs remain open. For example, this boundary is dynamic today
and is deliberately rejected by the first static checker:

```clojure klara-repl :norun
k=> (defaffine static-view [^:borrow x] (read x))
```

The invariant is value semantics: adding ownership to a successful
functional program preserves its observations (AF1); checked erasure must
preserve them too (AF3). See the [implementation report](../engineering/correctness.md)
for the exact tested boundary and remaining proof obligations.
