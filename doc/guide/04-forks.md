# 4. Forks and authority

Klara's central workflow is to fork a running world, work in the branch,
and then adopt or discard the result: try an edit without disturbing the
running system, run a counterfactual simulation, compare two strategies on
the same random numbers. This chapter shows snapshot forks of the world,
fork-resume of continuations, and the authority model of RFC 0001:
authorities that cannot be duplicated, the `fork` form with adoption,
settlement, and deferred irreversible effects. All of it runs in T0
(the reference interpreter, step S6); what is still design is listed at
the end.

## Snapshot forks (implemented)

A fork is a new world whose root starts as the parent's current root and
remembers that root as its pinned parent. Because roots are immutable and
share structure, forking shares the root rather than copying all definitions. After the fork, each side's
publications are invisible to the other.

The REPL can fork its current world and switch between worlds:

```clojure klara-repl
k=> (defn price [x] (* x 10))
#'price
k=> :repl/fork cheap
forked main -> cheap
k=> (defn price [x] (* x 7))
#'price
k=> (price 3)
21
k=> :repl/basis
cheap v2 (forked from main)
k=> :repl/switch main
switched to main
k=> (price 3)
30
```

From Klara code, `(perform :world/fork)` returns a fork of the world the code
runs in, and `(perform :world/eval-in w form)` evaluates or defines a quoted
form in a world or fiber:

```clojure klara-repl
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

```clojure klara-repl
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

```clojure klara-repl
k=> (handle [h {:split (fn [k] [(k :left) (k :right)])}]
      (let [x (perform h :split)] {:branch x :n (count (str x))}))
[{:n 5, :branch :left} {:n 6, :branch :right}]
```

Particle filters resample this way (`examples/klara/07-smc.md`). In T0,
continuations are vectors of data frames, so resuming one twice is cheap.
The second resumption is a *fork-resume*: it is allowed only when every
authority the continuation captured can be split (see below). On a
compiled host, RFC 0002 plans to resume CPS-compiled regions directly and
to replay from a savepoint behind host frames, never to clone JVM frames.

## Authority (implemented: RFC 0001)

Forking data is easy because data can be shared. The trouble is everything
that must not be duplicated: a file handle, a database branch that will be
merged, the weight of an observation, a budget, a random stream. RFC 0001
calls these **authorities**.

**Data is aliasable; authority is not.** An authority is an ordinary value
that may be referenced any number of times. What cannot be duplicated is
its *use*: each authority has exactly one state, kept in an authority
store, with the lifecycle open → advancing → settled | incomplete.

```clojure klara-repl
k=> (def r (resource "report.txt"))
#'r
k=> [r r {:again r}]
[#<resource> #<resource> {:again #<resource>}]
k=> (status r)
{:kind :resource, :status :open}
k=> (consume! r)
"report.txt"
k=> (consume! r)
!! authority: consume!: authority is settled (consume)
```

Copying `r` into a vector three times was fine; consuming it twice was
not. Because the check happens at the use, it does not matter how the
second use reached the authority: through another local, a nested
collection, metadata, a closure or a lookup in the world
(`test/klara/authority_test.clj` tries each).

There are five kinds. `resource` wraps a host object (consume it with
`consume!`, use it with `use!`); `evidence` holds likelihood mass (`spend!`,
`remaining`, `split`, `join`); `budget` holds components such as time and
money (`spend!`, `remaining`); `rand-key` is a splittable random key
(`draw!`); `branch!` makes a branchable authority over worlds (`system`,
`merge!`, `discard!`, `advance!`, `partition!`). `transfer!` moves any of
them to a new owner and makes the old value stale.

### The fork form

`(fork opts? [name expr ..] body..)` runs each `expr` as a branch, then
the body, in which each name is bound to its branch. `(:value b)` is the
branch's result. The body may `(adopt! b)` one branch; when the body
returns, the adopted branch is kept and the others are discarded. Without
a body, `fork` returns the branch values and discards every branch.

A fork **splits every authority** a branch uses, by kind, when the branch
first uses it:

| Authority | Split at fork |
|---|---|
| resource (file, channel, Java object) | none: transfer only (`:transfer {r i}`); a fork that needs it in two branches is rejected |
| branchable system (world, datahike, yggdrasil) | one branch per side; adopting merges it, the others are discarded |
| evidence (an observation's likelihood) | mass split by `:shares` (equal by default); populations join, then split |
| budget (time, memory, money) | split by `:shares`; hard components cannot be overspent |
| randomness (a splittable key) | split; shared only in a `:coupled` fork |

Evidence spent in a discarded branch is refunded; evidence spent in the
adopted branch is committed. Each branch can spend only its share:

```clojure klara-repl
k=> (def e (evidence 1))
#'e
k=> (fork [a (spend! e 1/4) b (remaining e)])
[1/4 1/2]
k=> (remaining e)
1
k=> (fork [a (spend! e 1/4) b (remaining e)] (adopt! a) (:value b))
1/2
k=> (remaining e)
3/4
```

A resource goes to exactly one branch, and only when the fork says so:

```clojure klara-repl
k=> (def f (resource :file))
#'f
k=> (fork [a (consume! f) b :other])
!! authority: resource authority was not transferred to this branch (a fork must transfer it to exactly one branch)
k=> (fork {:transfer {f 0}} [a (consume! f) b :other])
[:file :other]
k=> (status f)
{:kind :resource, :status :settled, :operation :consume}
```

Consuming a resource cannot be undone, so it stays consumed although the
branch was discarded. A random key is split per branch unless the fork is
`:coupled`; a budget's hard components are split, its traded ones may be
overspent and are charged to the parent either way:

```clojure klara-repl
k=> (def g (rand-key 42))
#'g
k=> (fork [a (draw! g) b (draw! g)])
[1424098507/2147483647 1606704301/2147483647]
k=> (fork :coupled [a (draw! g) b (draw! g)])
[1789310095/2147483647 1789310095/2147483647]
k=> (def b (budget {:seconds 10 :euros 4} #{:seconds}))
#'b
k=> (fork [x (spend! b {:seconds 6}) y 0])
!! authority: spend!: hard budget component :seconds would be overspent
k=> (fork [x (spend! b {:seconds 4}) y (spend! b {:euros 3})])
[{:seconds 1, :euros 2} {:seconds 5, :euros -1}]
k=> (remaining b)
{:seconds 6, :euros 1}
```

`examples/klara/08-coupled-fork.md` uses a coupled fork for a
counterfactual with common random numbers.

### Irreversible effects are deferred

Inside a branch, a host effect classified as irreversible (`println`,
`spit`, `swap!`, `reset!` and a few more) is not performed. It is queued
as an intent, run when the branch is adopted and dropped when it is
discarded. Acting at once needs a `capability`, which is a resource and so
goes to one branch only; each such action leaves a receipt.

```clojure klara-repl
k=> (fork [a (println "send offer A") b (println "send offer B")] (adopt! b) :sent)
send offer B
:sent
k=> (fork [a (println "send offer A")])
[#<intent clojure.core/println>]
k=> (def io (capability :mail))
#'io
k=> (fork {:transfer {io 0}} [a (direct io (println "logged now")) b :quiet])
logged now
[nil :quiet]
k=> (select-keys (last (receipts)) [:kind :op :args])
{:kind :direct, :op clojure.core/println, :args ["logged now"]}
```

### Settlement

A branchable authority governs branches of one or more systems. It is
settled exactly once, by `merge!` or `discard!`; repeating the same
settlement returns its result, anything else is refused:

```clojure klara-repl
k=> (def city (perform :world/fork))
#'city
k=> (def h (branch! {:city city}))
#'h
k=> (perform :world/eval-in (system h :city) '(def shops 2))
shops
k=> (merge! h)
{:merged [:city]}
k=> (perform :world/eval-in city 'shops)
2
k=> (discard! h)
!! authority: discard!: authority is settled (merge)
```

Settlement fails closed, following spindel's `ForkHandle`: a failure in the
read-only preflight (a conflict with a parent write) reopens the
authority; a failure after the first durable write leaves it
`:incomplete`, refusing any further settlement until it is recovered
explicitly. `partition!` splits one authority into parts that cover its
systems disjointly and exhaustively, and consumes the original;
`advance!` brings the parent's writes into the branch under an
`:advancing` lease.

### Fork-resume and authorities

A continuation resumed a second time runs as a branch too. Randomness is
split per resumption and a budget is borrowed, but a captured resource or
evidence authority cannot be split implicitly (for evidence, the number
of resumptions is unknown; split it explicitly before resuming), so the
second resumption is refused:

```clojure klara-repl
k=> (let [f (resource :file)]
      (handle [h {:split (fn [k] [(k :left) (k :right)])}]
        (let [x (perform h :split)] [x (status f)])))
!! authority: fork-resume: the continuation captured a resource authority, which cannot be split implicitly; it can be resumed only once
k=> (let [g (rand-key 7)]
      (handle [h {:split (fn [k] [(k :left) (k :right)])}]
        (let [x (perform h :split)] [x (draw! g)])))
[[:left 337897/2147483647] [:right 2041524840/2147483647]]
```

The check walks what the continuation holds (locals, collections,
metadata, closures). An authority it reaches only later, for example
through the world, is checked when it is used, as in a fork.

### What is and is not enforced today

| Obligation (RFC 0001) | Status |
|---|---|
| AU1 no program duplicates an authority | **enforced dynamically** in T0; adversarial suite in `authority_test` |
| AU2 settlement exactly once, fails closed | **enforced** for branchable authorities and every consuming operation; spindel's tests ported |
| AU3 partition is disjoint and exhaustive | **enforced** (`partition!`, and the adopt-one/discard-rest settlement of a fork) |
| AU4 snapshot isolation | **implemented** for worlds; tested |
| AU5 deferred intents run iff the branch is adopted | **enforced** for host calls classified irreversible; tested |
| AU6 evidence mass conserved across fork/resample/discard | **checked** by the store (split, join, fork, discard); property test |
| AU7 a static affine layer erases the dynamic checks | first owned-cell fragment tested (S10); broader authority checking remains open |

Linked Clojure state that is not wrapped in an authority (an atom read and
written through `deref` and host calls other than the irreversible ones,
a Java object) is still shared by all forks, as RFC 0001 documents for
compatibility level L0. `fork-following` (an overlay over the live
parent), receipts that Simmis review can consume, `within` and a
compensation story for effects that cannot be deferred remain design;
`doc/engineering/runtime.md` lists the open decisions.
