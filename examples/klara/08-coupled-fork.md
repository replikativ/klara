# 8. A coupled fork: close a shop

**Demonstrates:** forking the world to ask a counterfactual question ("what
happens to spending in Mitte if the Milaneo shopping centre closes?");
running the *same* function under two bases; common random numbers with a
`:coupled` fork, which shares a random key across its branches, against
an ordinary fork, which splits it.

**Exercises:** snapshot forks (RFC 0001 proposal item 2, obligation AU4:
no write after the fork is visible on the other side); basis-specific
execution (`doc/semantics.md` §9: an open definition runs under the basis
of whoever resolves it); the randomness row of RFC 0001's split table
(keys are split by default and shared only in a coupled fork), enforced
by T0's authority store (S6).

**Runs on:** T0, with the world operations `:world/fork` and
`:world/eval-in` (`klara.defs`) and the `fork` form.

## A toy city

Customers choose a shop with probability proportional to its
attractiveness and spend between 10 and 29 there. `spending` simulates `n`
customers and totals what they spend in one district. Its randomness comes
from `r`, a random key *authority* (`rand-key`): `(draw! r)` returns a
uniform number in (0, 1) and moves the key on. The key is a MINSTD
generator, the same as in example 7.

```klara-repl
k=> (def M 2147483647)
#'M
k=> (def shops [[:mitte 3] [:west 2] [:milaneo 5]])
#'shops
k=> (defn pick [u]
      (let [total (reduce + (map second shops))]
        (loop [ss shops acc 0]
          (let [[shop a] (first ss) acc (+ acc (/ a total))]
            (if (or (< u acc) (empty? (rest ss))) shop (recur (rest ss) acc))))))
#'pick
k=> (defn spending [r n district]
      (loop [i 0 total 0]
        (if (= i n)
          total
          (let [shop (pick (draw! r))
                k2 (long (* M (draw! r)))]
            (recur (inc i) (if (= shop district) (+ total 10 (mod k2 20)) total))))))
#'spending
k=> [(spending (rand-key 42) 500 :mitte) (spending (rand-key 42) 500 :milaneo)]
[3084 4735]
```

## Fork the world, close the shop

`(perform :world/fork)` takes a snapshot of the world as it is now: a new
world whose root starts as the current root and remembers it as its pinned
parent. Writing to the fork does not touch the session's world.

```klara-repl
k=> (def closed (perform :world/fork))
#'closed
k=> (perform :world/eval-in closed '(def shops [[:mitte 3] [:west 2]]))
shops
k=> shops
[[:mitte 3] [:west 2] [:milaneo 5]]
k=> (perform :world/eval-in closed 'shops)
[[:mitte 3] [:west 2]]
```

`spending` and `pick` were not redefined, yet asking the fork for
`spending` gives a function that sees the fork's `shops`. World definitions
are stored as open closures and run under the basis of whoever resolved
them; one and the same definition value now runs under two bases.

```klara-repl
k=> (def spending-closed (perform :world/eval-in closed 'spending))
#'spending-closed
k=> [(spending-closed (rand-key 42) 500 :mitte) (spending-closed (rand-key 42) 500 :milaneo)]
[5780 0]
```

## Shared versus split keys

The effect of the closure on Mitte is the difference between the branches.
In a **coupled** comparison both branches draw from the same key, so the
same customers draw the same numbers, and the difference measures the
intervention rather than the noise. In an **independent** comparison each
branch draws from its own split of the key.

Both are one `fork`. The key `r` is made outside the fork and used inside
both branches. An ordinary fork gives each branch its own split of `r`; a
fork with `:coupled` gives each branch the same key. Nothing is passed by
hand, and no branch can draw from the other's stream.

```klara-repl
k=> (defn effect [coupled? seed]
      (let [r (rand-key seed)]
        (fork {:coupled coupled?}
              [open (spending r 500 :mitte)
               shut (spending-closed r 500 :mitte)]
          (- (:value shut) (:value open)))))
#'effect
k=> [(effect true 1) (effect false 1)]
[2926 2752]
k=> (defn summary [xs]
      (let [n (count xs)
            mean (/ (reduce + xs) n)
            var (/ (reduce + (map (fn [x] (* (- x mean) (- x mean))) xs)) (dec n))]
        {:mean (Math/round (double mean)) :sd (Math/round (Math/sqrt var))}))
#'summary
k=> (summary (mapv (fn [seed] (effect true seed)) (range 1 41)))
{:mean 2940, :sd 152}
k=> (summary (mapv (fn [seed] (effect false seed)) (range 1 41)))
{:mean 2906, :sd 353}
```

Both estimate the same effect (the expected value is 500 × 0.3 × 19.5 =
2925), but the coupled estimates scatter less: the standard deviation over
40 keys drops from 353 to 152, so the same precision needs about a fifth of
the runs. A customer who would have shopped in Mitte anyway draws the same
amount on both sides, so only the customers who move from Milaneo
contribute to the coupled difference.

Within one world the same holds: two branches of an ordinary fork see
different customers, two branches of a coupled fork the same ones.

```klara-repl
k=> (def r (rand-key 3))
#'r
k=> (fork [a (spending r 10 :mitte) b (spending r 10 :mitte)])
[84 40]
k=> (fork :coupled [a (spending r 10 :mitte) b (spending r 10 :mitte)])
[14 14]
```

## What to notice

- **Snapshot, not following.** The fork pins the root at fork time. A
  later definition in the session is invisible in `closed`, and the
  fork's `shops` is invisible in the session (`world_ops_test`,
  `r4_test`). Following the live parent is a different, named operation
  in the design (`fork-following`), not implemented.
- **No shared namespace.** The parent's `spending` and the fork's are the
  same value; which `shops` it reads is decided by the basis it runs under.
  This is the fix for the leak experiment X1 measured in the prototype.
- **The key is an authority.** `r` is a value that both branches mention,
  but drawing from it is a use of the authority, and the fork decides what
  each branch's use means: a split key, or under `:coupled` the shared one.
  After the fork the parent's key has moved on, so the parent never
  repeats a stream it handed to a branch.
- **What is still by hand:** the world fork `closed` is a snapshot made
  with `:world/fork` and simply dropped at the end; wrapping it in a
  branchable authority (`branch!`) would let a fork adopt or discard it
  (`doc/guide/04-forks.md`, "Settlement"). `within` and its statistical
  guarantee are design.
