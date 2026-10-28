# 8. A coupled fork: close a shop

**Demonstrates:** forking the world to ask a counterfactual question ("what
happens to spending in Mitte if the Milaneo shopping centre closes?");
running the *same* function under two bases; common random numbers by
sharing a random key across the two branches, against split keys.

**Exercises:** snapshot forks (RFC 0001 proposal item 2, obligation AU4:
no write after the fork is visible on the other side); basis-specific
execution (`doc/semantics.md` §9: an open definition runs under the basis
of whoever resolves it); the randomness row of RFC 0001's split table
(keys are split by default and shared only in a coupled fork).

**Runs on:** T0, with the world operations `:world/fork` and
`:world/eval-in` (`klara.defs`). The `:coupled` fork *mode* of the design is
written out by hand here: we pass the same key to both branches ourselves.
Nothing tracks or enforces key splitting yet.

## A toy city

Customers choose a shop with probability proportional to its
attractiveness and spend between 10 and 29 there. `spending` simulates `n`
customers from a key and totals what they spend in one district.

```klara-repl
k=> (def M 2147483647)
#'M
k=> (defn next-key [key] (mod (* 48271 key) M))
#'next-key
k=> (defn split-key [key i] (next-key (mod (+ (* 1000003 key) i 1) M)))
#'split-key
k=> (defn uniform [key] (/ key M))
#'uniform
k=> (def shops [[:mitte 3] [:west 2] [:milaneo 5]])
#'shops
k=> (defn pick [u]
      (let [total (reduce + (map second shops))]
        (loop [ss shops acc 0]
          (let [[shop a] (first ss) acc (+ acc (/ a total))]
            (if (or (< u acc) (empty? (rest ss))) shop (recur (rest ss) acc))))))
#'pick
k=> (defn spending [key n district]
      (loop [i 0 key key total 0]
        (if (= i n)
          total
          (let [k1 (next-key key)
                k2 (next-key k1)
                shop (pick (uniform k1))]
            (recur (inc i) k2 (if (= shop district) (+ total 10 (mod k2 20)) total))))))
#'spending
k=> [(spending 42 500 :mitte) (spending 42 500 :milaneo)]
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
k=> [(spending-closed 42 500 :mitte) (spending-closed 42 500 :milaneo)]
[5780 0]
```

## Shared versus split keys

The effect of the closure on Mitte is the difference between the branches.
In a **coupled** comparison both branches get the same key, so the same
customers draw the same numbers, and the difference measures the
intervention rather than the noise. In an **independent** comparison each
branch gets its own split of the key.

```klara-repl
k=> (defn coupled [key] (- (spending-closed key 500 :mitte) (spending key 500 :mitte)))
#'coupled
k=> (defn independent [key]
      (- (spending-closed (split-key key 1) 500 :mitte) (spending (split-key key 2) 500 :mitte)))
#'independent
k=> (defn summary [xs]
      (let [n (count xs)
            mean (/ (reduce + xs) n)
            var (/ (reduce + (map (fn [x] (* (- x mean) (- x mean))) xs)) (dec n))]
        {:mean (Math/round (double mean)) :sd (Math/round (Math/sqrt var))}))
#'summary
k=> (summary (mapv coupled (range 1 41)))
{:mean 2940, :sd 152}
k=> (summary (mapv independent (range 1 41)))
{:mean 2898, :sd 269}
```

Both estimate the same effect (the expected value is 500 × 0.3 × 19.5 =
2925), but the coupled estimates scatter less: the standard deviation over
40 keys drops from 269 to 152, so the same precision needs about a third of
the runs. A customer who would have shopped in Mitte anyway draws the same
amount on both sides, so only the customers who move from Milaneo
contribute to the coupled difference.

## What to notice

- **Snapshot, not following.** The fork pins the root at fork time. A
  later definition in the session is invisible in `closed`, and the
  fork's `shops` is invisible in the session (`world_ops_test`,
  `r4_test`). Following the live parent is a different, named operation
  in the design (`fork-following`), not implemented.
- **No shared namespace.** The parent's `spending` and the fork's are the
  same value; which `shops` it reads is decided by the basis it runs under.
  This is the fix for the leak experiment X1 measured in the prototype.
- **Design, not yet enforced:** in RFC 0001 the random key is an
  *authority*. A fork splits it automatically, and only a fork declared
  `:coupled` shares it. Here keys are ordinary numbers passed by hand, so
  nothing stops a program from reusing a key by accident. The branches
  are also not settled (adopted or discarded); `closed` is simply dropped.
