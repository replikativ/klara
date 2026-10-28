# Example 3: fib and gibonacci with let-insertion

Specializing the Fibonacci recurrence to `n` is the standard example of code
duplication in staging. The naive generator splices the code of `fib (n-1)` and
`fib (n-2)` into a sum, and each of these again contains both of its
predecessors, so the generated expression has exponential size. Let-insertion
fixes this. It binds each intermediate result once and refers to it by name.
`genletrec` goes further and generates a group of mutually recursive functions,
one per key, memoized at generation time.

"Gibonacci" is the generalized Fibonacci function with arbitrary first values
`x` and `y`, so the two seeds are run-time values too.

## Naive: duplication

```klara-repl
k=> (def nfib
      (fn [n x y]
        (cond (= n 0) x
              (= n 1) y
              :else (code (+ (esc (nfib (- n 1) x y)) (esc (nfib (- n 2) x y)))))))
#'nfib
k=> (code (fn [x y] (esc (nfib 5 (code x) (code y)))))
(code (fn [x_1 y_2] (+ (+ (+ (+ y_2 x_1) y_2) (+ y_2 x_1)) (+ (+ y_2 x_1) y_2))))
```

## With genlet: one binding per intermediate

The generator memoizes on `n` in a present-stage table and let-binds each sum.
`genlet` places every binding directly under `fn [x y]`, the highest point
where `x` and `y` are in scope, and in dependency order.

```klara-repl
k=> (def lfib
      (fn [n x y]
        (let [memo (atom {})]
          (letfn [(f [n]
                    (or (get @memo n)
                        (let [c (cond (= n 0) x
                                      (= n 1) y
                                      :else (genlet (code (+ (esc (f (- n 1))) (esc (f (- n 2)))))))]
                          (swap! memo assoc n c)
                          c)))]
            (f n)))))
#'lfib
k=> :code (code (fn [x y] (esc (lfib 5 (code x) (code y)))))
(fn [x_1 y_2]
  (let [t_3 (+ y_2 x_1)
        t_4 (+ t_3 y_2)
        t_5 (+ t_4 t_3)
        t_6 (+ t_5 t_4)]
    t_6))
k=> ((run (code (fn [x y] (esc (lfib 5 (code x) (code y)))))) 1 1)
8
```

Code size, measured in nodes of the generated term, for `n = 5, 10, 15`:

```klara-repl
k=> (mapv (fn [n] [(code-size (code (fn [x y] (esc (nfib n (code x) (code y))))))
                   (code-size (code (fn [x y] (esc (lfib n (code x) (code y))))))])
          [5 10 15])
[[16 18] [178 38] [1974 58]]
```

The naive size grows like `fib n` (exponentially). With let-insertion it grows
by 4 nodes per step of `n`.

## With genletrec: generating the recursive functions

The BER MetaOCaml version of the same example (`test/genletrec.ml`) keeps the
recursion in the generated code but specializes it. `with-genletrec` opens a
locus for a `letfn` group. Inside it, `(g gen k)` returns the code of the
function generated for key `k`, and calls `(gen k)` only the first time it sees
`k`. The generated functions refer to each other by name, so the group can be
mutually recursive. The memoization is also what makes generation terminate
here: Ackermann specialized to `m` would otherwise unfold forever.

```klara-repl
k=> (def sfib
      (fn [n]
        (with-genletrec [g]
          (letfn [(gen [n]
                    (cond (= n 0) (code (fn [x y] x))
                          (= n 1) (code (fn [x y] y))
                          :else (code (fn [x y] (+ ((esc (g gen (- n 1))) x y)
                                                   ((esc (g gen (- n 2))) x y))))))]
            (code (fn [x y] ((esc (g gen n)) x y)))))))
#'sfib
k=> :code (sfib 5)
(letfn
  [(h_1 [x_7 y_8] (+ (h_2 x_7 y_8) (h_3 x_7 y_8)))
   (h_2 [x_9 y_10] (+ (h_3 x_9 y_10) (h_4 x_9 y_10)))
   (h_3 [x_11 y_12] (+ (h_4 x_11 y_12) (h_5 x_11 y_12)))
   (h_4 [x_13 y_14] (+ (h_5 x_13 y_14) (h_6 x_13 y_14)))
   (h_5 [x_15 y_16] y_16)
   (h_6 [x_17 y_18] x_17)]
  (fn [x_19 y_20] (h_1 x_19 y_20)))
k=> ((run (sfib 5)) 1 1)
8
k=> (mapv (fn [n] (code-size (sfib n))) [5 10 15])
[50 100 150]
```

```klara-repl
k=> (def sack
      (fn [m]
        (with-genletrec [g]
          (letfn [(gen [m]
                    (if (= m 0)
                      (code (fn [n] (+ n 1)))
                      (code (fn [n] (if (= n 0)
                                      ((esc (g gen (- m 1))) 1)
                                      ((esc (g gen (- m 1))) ((esc (g gen m)) (- n 1))))))))]
            (g gen m)))))
#'sack
k=> :code (sack 2)
(letfn
  [(h_1 [n_4] (if (= n_4 0) (h_2 1) (h_2 (h_1 (- n_4 1)))))
   (h_2 [n_5] (if (= n_5 0) (h_3 1) (h_3 (h_2 (- n_5 1)))))
   (h_3 [n_6] (+ n_6 1))]
  h_1)
k=> ((run (sack 2)) 3)
9
```

A generated binding may mention only variables that are in scope at its locus.
Here the function for key `1` mentions `z`, which is bound *inside* the
`with-genletrec`, and the check refuses it:

```klara-repl
k=> (with-genletrec [g]
      (code (fn [z] (esc (g (fn [k] (code (fn [] z))) 1)))))
!! scope-extrusion: code mentions z, whose binder is not in scope at the with-genletrec that binds it (a variable escaped the code that binds it)
```

## What it demonstrates

- Code duplication under naive staging, measured with `code-size`.
- `genlet`. A binding floats to the highest locus where its free variables
  are bound, which for `lfib` is just under `fn [x y]`.
- `with-genletrec` (BER's `with_locus_rec`/`mkgenlet`). Memoized generation
  of mutually recursive definitions whose number is known only at generation
  time.
- The scope-extrusion check for let-inserted names. They live as long as
  their locus.

## References

- Y. Kameyama, O. Kiselyov and C. Shan, "Shifting the stage: staging with
  delimited control", PEPM 2009 (extended in *JFP* 21(6), 2011). This is
  let-insertion in multi-stage programming.
- J. Yallop and O. Kiselyov, "Generating mutually recursive definitions",
  PEPM 2019.
- O. Kiselyov and J. Yallop, "let (rec) insertion without effects, lights or
  magic", arXiv:2201.00495, 2022.
- BER MetaOCaml N153, `test/genlet.ml` and `test/genletrec.ml`. The
  examples above are ports of `sfib` and `sack`.
