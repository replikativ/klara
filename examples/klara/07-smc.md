# 7. Sequential Monte Carlo with fork and resampling

**Demonstrates:** probabilistic programming with `choose` and `observe` as
*user* effects, interpreted by a handler written in Klara; resampling as
**fork-resume**, where a suspended particle's continuation is resumed several
times, once per child; splittable random keys; evidence bookkeeping by
"join, then split".

**Exercises:** the handler rules `Handle`, `Op` and `return`
(`doc/semantics.md` §3): deep handlers and multi-shot continuations;
lexical targeting (EF4, RFC 0002); the evidence rule of RFC 0001 (AU6:
mass is conserved across the population, not per particle) and its
fork-resume rule (a continuation is resumed more than once only when what
it captured can be split), both checked by T0's authority store (S6).

**Runs on:** T0 only. Nothing here is compiled; the 1000-particle run takes
about a second.

## The model

A two-state hidden Markov model: is it raining (`true`) or not? The weather
persists with probability 4/5. Each day we see an umbrella with probability
9/10 if it rains and 1/5 if it does not. The program is ordinary Klara; the
inference effects are performed on the handler instance `m` it receives.

```klara-repl
k=> (defn hmm [m ys]
      (loop [x (perform m :choose 1/2) ys ys]
        (perform m :observe (if x 9/10 1/5) (first ys))
        (if (empty? (rest ys))
          x
          (recur (perform m :choose (if x 4/5 1/5)) (rest ys)))))
#'hmm
k=> (def ys [true true false true true])
#'ys
```

`(perform m :choose p)` asks for a Boolean that is `true` with probability
`p`. `(perform m :observe p y)` says the observed Boolean `y` has
probability `p` of being `true`. Neither says *how* to answer; that is the
handler's business.

## Random keys

Randomness is a pure, splittable key (a MINSTD generator), never hidden
state. A key is split per particle and per child, so two branches never
share a stream unless asked to (example 8 asks to).

```klara-repl
k=> (def M 2147483647)
#'M
k=> (defn next-key [key] (mod (* 48271 key) M))
#'next-key
k=> (defn split-key [key i] (next-key (mod (+ (* 1000003 key) i 1) M)))
#'split-key
k=> (defn uniform [key] (/ key M))
#'uniform
```

## The particle handler

A particle is the model run under a handler that

- answers `:choose` by drawing from the key and resuming (`k` called once,
  in tail position);
- answers `:observe` by **not** resuming: it returns the continuation `k`
  together with the likelihood of the observation as the particle's weight.
  The particle is now a suspended computation, a plain value;
- answers `:return` with the final value.

The handler is written in state-passing style: every clause returns a
function of the current key.

```klara-repl
k=> (defn particle [model]
      (handle [m {:choose  (fn [p k]
                             (fn [key]
                               (let [key2 (next-key key)]
                                 ((k (< (uniform key2) p)) key2))))
                  :observe (fn [p y k]
                             (fn [key] {:k k :key key :w (if y p (- 1 p))}))
                  :return  (fn [x] (fn [key] {:done x :key key}))}]
        (model m)))
#'particle
k=> (def p0 ((particle (fn [m] (hmm m ys))) 7))
#'p0
k=> (:w p0)
9/10
```

Particle `p0` drew "rain" on day 0 and is suspended at the first
observation (an umbrella), which then has likelihood 9/10. Resuming it means calling its
continuation; the handler is reinstalled (deep), so the particle runs on to
the next `observe` and suspends again:

```klara-repl
k=> (defn resume [p key] (((:k p) nil) key))
#'resume
k=> (:w (resume p0 (split-key 7 0)))
9/10
```

Because `k` is a value, it can be resumed more than once. That is how
resampling forks a particle: one parent continuation, several children,
each with its own split key.

## Resampling and the SMC loop

Systematic resampling selects `n` children from the weighted population
with one uniform draw. The evidence is handled collectively: the total
weight `W` of the population is joined, and each child gets the equal share
`W/n`. Mass is conserved for the population (AU6), not for each parent; the
running product of `W/n` is the estimate of the marginal likelihood `z`.

```klara-repl
k=> (defn resample [ps u]
      (let [n (count ps) total (reduce + (map :w ps))]
        (loop [j 0 i 0 acc (:w (first ps)) out []]
          (if (= j n)
            out
            (let [pos (* (/ (+ u j) n) total)]
              (if (< acc pos)
                (recur j (inc i) (+ acc (:w (nth ps (inc i)))) out)
                (recur (inc j) i acc (conj out (nth ps i)))))))))
#'resample
k=> (defn smc [model n key]
      (loop [ps (mapv (fn [i] ((particle model) (split-key key i))) (range n))
             key key
             z 1]
        (if (:done (first ps))
          {:p-true (/ (count (filter (fn [p] (true? (:done p))) ps)) n)
           :z (double z)}
          (let [key2 (next-key key)
                total (reduce + (map :w ps))
                kids (resample ps (uniform key2))]
            (recur (vec (map-indexed (fn [i p] (resume p (split-key (:key p) i))) kids))
                   key2
                   (* z (/ total n)))))))
#'smc
```

## Checking against the exact answer

For a model this small the forward algorithm gives the exact posterior
probability that it rains on the last day, in rationals:

```klara-repl
k=> (defn exact [ys]
      (loop [f {true 1/2 false 1/2} ys ys z 1]
        (let [y (first ys)
              lik (fn [x] (let [p (if x 9/10 1/5)] (if y p (- 1 p))))
              g {true (* (f true) (lik true)) false (* (f false) (lik false))}
              s (+ (g true) (g false))]
          (if (empty? (rest ys))
            {:p-true (/ (g true) s) :z (double (* z s))}
            (recur {true  (/ (+ (* (g true) 4/5) (* (g false) 1/5)) s)
                    false (/ (+ (* (g true) 1/5) (* (g false) 4/5)) s)}
                   (rest ys)
                   (* z s))))))
#'exact
k=> (exact ys)
{:p-true 279711/316123, :z 0.030347808}
k=> (double (:p-true (exact ys)))
0.8848169857935044
k=> (let [r (smc (fn [m] (hmm m ys)) 1000 42)] [(double (:p-true r)) (:z r)])
[0.896 0.03006428601588098]
k=> (mapv (fn [seed] (double (:p-true (smc (fn [m] (hmm m ys)) 200 seed)))) [1 2 3 4 5 6])
[0.865 0.895 0.895 0.91 0.86 0.86]
```

The estimates scatter around 0.885 and tighten with more particles. Every
run is reproducible: the only randomness is the key.

## What fork-resume checks

Resampling resumes one continuation several times. T0 allows this only
when everything the continuation captured can be split. These particles
hold plain values, so every resumption above was admitted. A particle that
holds a resource, here a log file, may be resumed once, but resampling it
into two children is refused before the second child runs:

```klara-repl
k=> (def log (resource :log))
#'log
k=> (def p1 ((particle (fn [m] (let [f log] [(hmm m ys) f]))) 7))
#'p1
k=> (:w (resume p1 (split-key 7 0)))
9/10
k=> (:w (resume p1 (split-key 7 1)))
!! authority: fork-resume: the continuation captured a resource authority, which cannot be split implicitly; it can be resumed only once
```

Evidence is splittable, but not implicitly: how much mass each child gets
depends on how many children there are, which a continuation cannot know.
The population does it explicitly, as `smc` does with plain numbers: join
the weights, then split the total. As authorities, the parts are used up
by the join, so no weight can be counted twice:

```klara-repl
k=> (def ws (mapv (fn [w] (evidence w)) [1/10 3/10 2/5 1/5]))
#'ws
k=> (def total (join ws))
#'total
k=> (remaining total)
1
k=> (mapv (fn [e] (remaining e)) (split total 4))
[1/4 1/4 1/4 1/4]
k=> (status (first ws))
{:kind :evidence, :status :settled, :operation :join}
k=> (join ws)
!! authority: join: authority is settled (join)
```

## What to notice

- **The model knows nothing about inference.** `hmm` performs two
  operations on an instance it was given. Another handler (exact
  enumeration by resuming `k` with both `true` and `false`, or importance
  sampling) would reuse it unchanged.
- **Lexical targeting.** `m` is the instance bound by `handle`. A library
  handler for `:choose` installed between `particle` and the model would not
  intercept these performs (EF4; `doc/guide/03-effects.md`).
- **Fork-resume.** A particle is a continuation plus a key and a weight. The
  same continuation is resumed once per child. In T0 continuations are
  vectors of data frames, so this is cheap; every resumption after the
  first is checked (previous section).
- **Weights and keys are still plain numbers here.** The loop does its
  bookkeeping by hand, which is correct by construction; moving `:w` to
  evidence authorities and the key to a `rand-key` would let the store
  check it too, at the cost of a store transition per particle and step.
- `mapv` and `map-indexed` are clojure.core functions called with Klara
  closures. The closures run in nested machines; this is fine because the
  handler is *inside* each particle. A perform aimed at a handler outside
  the host call would be a detected error (EF5).
