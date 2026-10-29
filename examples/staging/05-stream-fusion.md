# Example 5: stream fusion by staging

A pipeline such as `range → map → filter → take → sum` written with
sequence functions builds an intermediate sequence at every stage. Strymonas
(Kiselyov, Biboudis, Palladinos and Smaragdakis) makes the pipeline a
*generator* instead. Each combinator is a present-stage function that
contributes a piece of a single loop, and the generated code has no
intermediate structures, no closures per element, and no stage boundaries.
The paper shows that this works for the complete set of combinators, including
`take`, nested `flat_map` and `zip`, and that the generated code matches
hand-written loops.

This example implements the linear fragment: `from-range`, `smap`,
`sfilter`, `stake` and `sfold`.

## Streams as loop generators

A stream is a map with one entry, `:loop`. Given a list of extra termination
conditions (code of booleans) and a consumer `k` (from the code of an element
to the code of a statement), it generates the whole loop. `from-range` owns the
loop variable. The other combinators wrap the consumer, and `stake` adds a
counter and a termination condition.

```clojure klara-repl
k=> (def all-of
      (fn [conds] (reduce (fn [a c] (code (if (esc a) (esc c) false))) conds)))
#'all-of
k=> (def from-range
      (fn [lo hi]
        {:loop (fn [conds k]
                 (code (loop [i (esc lo)]
                         (if (esc (all-of (cons (code (< i (esc hi))) conds)))
                           (do (esc (k (code i)))
                               (recur (inc i)))
                           nil))))}))
#'from-range
k=> (def smap
      (fn [f s]
        {:loop (fn [conds k]
                 ((:loop s) conds (fn [x] (code (let [y (esc (f x))] (esc (k (code y))))))))}))
#'smap
k=> (def sfilter
      (fn [p s]
        {:loop (fn [conds k]
                 ((:loop s) conds (fn [x] (code (if (esc (p x)) (esc (k x)) nil)))))}))
#'sfilter
k=> (def stake
      (fn [n s]
        {:loop (fn [conds k]
                 (code (let [left (atom (esc n))]
                         (esc ((:loop s) (cons (code (pos? @left)) conds)
                                         (fn [x] (code (do (swap! left dec) (esc (k x))))))))))}))
#'stake
k=> (def sfold
      (fn [f z s]
        (code (let [acc (atom (esc z))]
                (do (esc ((:loop s) [] (fn [x] (code (reset! acc (esc (f (code @acc) x)))))))
                    @acc)))))
#'sfold
```

`smap` let-binds each mapped element, so a consumer that uses its element
twice does not duplicate the work. The termination condition of `stake` is
generated *inside* the `let` that binds its counter `left` and is spliced into
the loop guard. That is legal because the loop is generated inside the same
`let`, which the scope check confirms on splice.

## One pipeline, one loop

```clojure klara-repl
k=> (def pipeline
      (code (fn [n]
              (esc (sfold (fn [a x] (code (+ (esc a) (esc x))))
                          (code 0)
                          (stake (code 3)
                                 (sfilter (fn [x] (code (even? (esc x))))
                                          (smap (fn [x] (code (* (esc x) (esc x))))
                                                (from-range (code 0) (code n))))))))))
#'pipeline
k=> :repl/code pipeline
(fn [n_1]
  (let [acc_2 (atom 0)
        _ (let [left_3 (atom 3) i_4 0]
            (loop [i_5 i_4]
              (if (if (< i_5 n_1) (pos? (deref left_3)) false)
                (do
                  (let [y_6 (* i_5 i_5)]
                    (if (even? y_6)
                      (do
                        (swap! left_3 dec)
                        (reset! acc_2 (+ (deref acc_2) y_6)))))
                  (recur (inc i_5))))))]
    (deref acc_2)))
k=> ((run pipeline) 1000000)
20
k=> (reduce + (take 3 (filter even? (map (fn [x] (* x x)) (range 1000000)))))
20
```

The generated loop stops after the third even square: `take` is part of the
loop condition, so the remaining 999 997 iterations never run. The generated
code mutates two atoms, exactly as strymonas generates OCaml references or C
variables. The mutation is local to the generated function.

## Relation to S3's certified fusion

`doc/engineering/correctness.md` fuses the same kind of pipeline in a different way.
There the user writes an ordinary `map`/`filter`/`reduce` pipeline, the
compiler elaborates it into the ansatz kernel, rewrites it with two fusion laws
proved there (`foldl_map`, `foldl_filter`), and installs the fused function
with a certificate that the kernel rechecks. The two approaches put trust in
different places:

| | S3 certified fusion | Staged streams (this example) |
|---|---|---|
| Who fuses | the optimizer, transparently | the library, by construction |
| What the user writes | ordinary sequence code | stream combinators |
| Why it is correct | a kernel-checked proof per optimization | the generator's code, which is not verified |
| Coverage | map, filter and reduce over `(List Nat)`, pure stages | anything the combinators generate, including effects in stages and `take` |
| Fallback | guards and the generic path | none needed: the generated code *is* the program |

A natural combination is a staged generator whose output is checked by S3's
machinery: the generator proposes the fused loop, and a certificate relates it
to the unfused pipeline. That is open.

## What it demonstrates

- Fusion as generation. Combinators are present-stage functions, and the only
  thing left at run time is one loop.
- Generated mutable state (`atom`) whose binders are introduced by one
  combinator and used by another, with the scope check confirming each splice.
- Code built across several cooperating generators: `stake` adds to the guard
  that `from-range` emits.

Not covered: `zip` of two producers and nested `flat_map`, the parts of
strymonas that need its producer normal forms (unfold-style and for-style
producers with explicit linearity). They are the reason for the paper's "to
completeness".

## References

- O. Kiselyov, A. Biboudis, N. Palladinos and Y. Smaragdakis, "Stream fusion,
  to completeness", POPL 2017.
- `doc/engineering/correctness.md`: map/filter/reduce fusion with ansatz
  certificates.
