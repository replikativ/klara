# 4. Forks and authority

Klara's central workflow is to fork a running world, work in the branch,
and then adopt or discard the result: try an edit without disturbing the
running system, run a counterfactual simulation, compare two strategies on
the same random numbers. This chapter shows what a fork is today
(**implemented**: snapshot forks of the world, bases, fork-resume of
continuations) and what RFC 0001 adds on top (**design**: authorities that
cannot be duplicated, deferred irreversible effects, settlement).

## Snapshot forks (implemented)

A fork is a new world whose root starts as the parent's current root and
remembers that root as its pinned parent. Because roots are immutable and
share structure, forking costs nothing. After the fork, each side's
publications are invisible to the other.

The REPL can fork its current world and switch between worlds:

```klara-repl
k=> (defn price [x] (* x 10))
#'price
k=> :fork cheap
forked main -> cheap
k=> (defn price [x] (* x 7))
#'price
k=> (price 3)
21
k=> :basis
cheap v2 (forked from main)
k=> :switch main
switched to main
k=> (price 3)
30
```

From Klara code, `(perform :world/fork)` returns a fork of the world the code
runs in, and `(perform :world/eval-in w form)` evaluates or defines a quoted
form in a world or fiber:

```klara-repl
k=> (def w (perform :world/fork))
#'w
k=> (perform :world/eval-in w '(defn price [x] (* x 12)))
price
k=> [(price 3) (perform :world/eval-in w '(price 3))]
[30 36]
k=> (defn price [x] (* x 11))
#'price
k=> [(price 3) (perform :world/eval-in w '(price 3))]
[33 36]
```

The last line shows both directions of isolation: the parent's later
definition does not reach the fork, and the fork's never reached the
parent (obligation AU4, "no parent write after the fork is visible in the
branch"; tested in `r4_test` and `world_ops_test`, conjectured in general).

**One definition, two bases.** A function taken from the fork runs under
the fork's basis, even though the fork never redefined it:

```klara-repl
k=> (defn quote-for [n] (str n " items cost " (price n)))
#'quote-for
k=> (def w2 (perform :world/fork))
#'w2
k=> (perform :world/eval-in w2 '(defn price [x] 0))
price
k=> [(quote-for 2) ((perform :world/eval-in w2 'quote-for) 2)]
["2 items cost 22" "2 items cost 0"]
```

`quote-for` is stored once, as an open closure. Whoever resolves it decides
which `price` it calls. There is no shared namespace through which one
branch could leak into another; the prototype before S1 had exactly that
leak (experiment X1).

**Meaning.** The spec's configuration carries the world as a value, so a
snapshot fork is just running two configurations with the same world. The
square "forking commutes with the world" (`doc/semantics.md` §8) is tested
for the snapshot part.

## Fork-resume (implemented)

A continuation captured by a handler is a value. Resuming it twice runs the
rest of the computation twice, from the same state: a fork of the
computation rather than of the world.

```klara-repl
k=> (handle [h {:split (fn [k] [(k :left) (k :right)])}]
      (let [x (perform h :split)] {:branch x :n (count (str x))}))
[{:n 5, :branch :left} {:n 6, :branch :right}]
```

Particle filters resample this way (`examples/klara/07-smc.md`). In T0,
continuations are vectors of data frames, so resuming one twice is safe.
On a compiled host, RFC 0002 plans to resume CPS-compiled regions directly
and to replay from a savepoint behind host frames, never to clone JVM
frames.

## Authority (design: RFC 0001)

Forking data is easy because data can be shared. The trouble is everything
that must not be duplicated: a file handle, a database branch that will be
merged, the weight of an observation, a budget, a random stream. RFC 0001
calls these **authorities**.

- **Data is aliasable; authority is not.** Any value may be referenced any
  number of times. An authority is a token with a lifecycle
  (open → advancing → settled | incomplete) and can be used up exactly once.
- **A fork splits every authority** the forked computation holds, by kind:

  | Authority | Split at fork |
  |---|---|
  | resource (file, channel, Java object) | none: transfer only; a fork that needs it in both branches is rejected |
  | branchable system (world, datahike, yggdrasil) | one branch per side; settlement authority partitioned |
  | evidence (an observation's likelihood) | mass-preserving split; populations join, then split |
  | budget (time, memory, money) | split; hard components cannot be overspent |
  | randomness (a splittable key) | split; shared only in a `:coupled` fork |

- **Irreversible effects are deferred.** Inside a fork, host I/O (sending an
  email) is queued as an intent, executed if the branch is adopted and
  dropped if it is discarded.
- **Settlement** of each authority happens exactly once and fails closed.
- **Multi-shot resumption** is allowed only when the captured computation's
  authorities can be split.

The surface is not fixed. A sketch of the city example of
`doc/background/02-examples.md`:

```klara-repl :norun
k=> (fork :coupled [w (scenario/close city :milaneo)]
      (within {:rel 0.01}
        (- (spending city :mitte) (spending w :mitte))))
{:value 2925.4 :guarantee :statistical :receipt {..}}
```

This block cannot run: `fork` as a form, `:coupled`, `within` and receipts
do not exist yet. `examples/klara/08-coupled-fork.md` writes the same
experiment with what exists, passing the shared key by hand.

### What is and is not enforced today

| Obligation (RFC 0001) | Status |
|---|---|
| AU1 no program duplicates an authority | **not enforced**: there are no authority tokens; a continuation holding a Java object can be resumed twice |
| AU2 settlement exactly once, fails closed | holds in spindel; not ported |
| AU3 partition is disjoint and exhaustive | holds in spindel; not ported |
| AU4 snapshot isolation | **implemented** for worlds; tested |
| AU5 deferred intents run iff the branch is adopted | not implemented; host effects in a fork run immediately |
| AU6 evidence mass conserved across fork/resample | by construction in example 7's handler; not checked by the runtime |
| AU7 a static affine layer erases the dynamic checks | not implemented |

A fork today is therefore safe for **values and world definitions**. Linked
Clojure state (atoms, Java objects, I/O) is shared by all forks, as RFC 0001
documents for compatibility level L0. A forked branch is not adopted or
discarded either; an unused fork is simply garbage.
