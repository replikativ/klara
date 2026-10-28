# Example 2: dot product and matrix-vector product with a known matrix

The scientific-computing loop from the Shonan Challenge: multiply a vector
known only at run time by a matrix known at generation time, as when a
stencil, a filter or the transition matrix of a hidden Markov model is fixed.
A generic loop does `n*m` multiplications. A specialized one unrolls the loops,
drops the zero entries, and multiplies by 1 without a multiplication. Kiselyov
develops this example in MetaOCaml, including partial unrolling and output to
C.

## Dot product with a static row

```klara-repl
k=> (def sdot
      (fn [row x]
        (let [terms (keep-indexed
                      (fn [j a]
                        (cond (zero? a) nil
                              (= a 1) (x j)
                              :else (code (* a (esc (x j))))))
                      row)]
          (if (empty? terms)
            (code 0)
            (reduce (fn [acc t] (code (+ (esc acc) (esc t)))) terms)))))
#'sdot
```

`row` is a present vector of numbers. `x` is a present function from a column
index to the code of that vector element. `a` and `j` are present numbers that
appear inside `code`, so they are lifted into the generated code as literals
(cross-stage persistence). The loop over `row` runs at generation time, which
unrolls it.

```klara-repl
k=> (code (fn [v] (esc (sdot [1 0 2 0] (fn [j] (code (nth v j)))))))
(code (fn [v_1] (+ (nth v_1 0) (* 2 (nth v_1 2)))))
```

Here `keep-indexed` and `reduce` are host functions that call back into Klara
closures, and those closures build code. The binder `v` is still in scope for
them.

## Matrix-vector product

Every row reads the same vector elements. The generator loads each element
that some row uses exactly once: it memoizes `x` and let-binds each element
with `genlet`. Elements that no row uses are never loaded.

```klara-repl
k=> (def smv
      (fn [m]
        (code
          (fn [v]
            (esc
              (let [loaded (atom {})
                    x (fn [j]
                        (or (get @loaded j)
                            (let [c (genlet (code (nth v j)))]
                              (swap! loaded assoc j c)
                              c)))]
                (code-vector (mapv (fn [row] (sdot row x)) m))))))))
#'smv
k=> (def m [[1 0 2 0]
            [0 0 0 0]
            [0 3 1 0]])
#'m
k=> :repl/code (smv m)
(fn [v_1]
  (let [t_2 (nth v_1 0) t_3 (nth v_1 2) t_4 (nth v_1 1)]
    [(+ t_2 (* 2 t_3)) 0 (+ (* 3 t_4) t_3)]))
k=> ((run (smv m)) [10 20 30 40])
[70 0 90]
```

The unspecialized product gives the same result:

```klara-repl
k=> (def mv (fn [m v] (mapv (fn [row] (reduce + (map * row v))) m)))
#'mv
k=> (mv m [10 20 30 40])
[70 0 90]
```

`code-vector` builds the code of a vector from a sequence of code values whose
length is known only at generation time. The scope check still applies to the
elements: they are checked when the vector is spliced or run.

## What it demonstrates

- Loop unrolling and constant folding as ordinary generation-time computation.
- Implicit cross-stage persistence of present numbers (`a`, `j`).
- Code built inside host higher-order functions (`keep-indexed`, `mapv`), and
  let-insertion from inside them.
- Memoized let-insertion. A present-stage table (an atom) decides what the
  generated code computes once.

C generation is future work. The generated code above uses only `nth`,
arithmetic and vectors, which is the fragment that BER MetaOCaml's offshoring
translates to C (`ber-metaocaml-153/offshoring.ml`, tests in
`test/offshore*.ml`). In Klara, the corresponding route is the K3 back end.

## References

- B. Aktemur, Y. Kameyama, O. Kiselyov and C. Shan, "Shonan challenge for
  generative programming: short position paper", PEPM 2013.
- O. Kiselyov, "Reconciling abstraction with high performance: a MetaOCaml
  approach", *Foundations and Trends in Programming Languages* 5(1), 2018.
- O. Kiselyov, "Generating C: system description", FLOPS 2022, LNCS 13215;
  extended as "Generating C: heterogeneous metaprogramming system description",
  *Science of Computer Programming* 231, 2024.
