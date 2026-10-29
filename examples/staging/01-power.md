# Example 1: power

The oldest example of program specialization: `x^n` with the exponent `n`
known early and the base `x` known late. Ershov used it to explain mixed
computation, and it is the first example in every MetaOCaml tutorial.
Specializing `power` to `n` removes the recursion on `n` and leaves a
straight-line product.

## Source

```clojure klara-repl
k=> (def power
      (fn [n x]
        (if (zero? n)
          (code 1)
          (code (* (esc x) (esc (power (dec n) x)))))))
#'power
```

`n` is a present value, and the recursion on it runs at generation time.
`x` is a code value. Each step builds `(* x <rest>)`, where `esc` splices the
code of `x` and the code of the recursive call.

## Generated code

```clojure klara-repl
k=> (code (fn [y] (esc (power 3 (code y)))))
(code (fn [y_1] (* y_1 (* y_1 (* y_1 1)))))
k=> (def power7 (run (code (fn [y] (esc (power 7 (code y)))))))
#'power7
k=> (power7 2)
128
```

The residual `(fn [y] (* y (* y ...)))` contains no test of `n` and no call.
`run` compiled the closed code under the current basis, and `power7` is an
ordinary function.

The trailing `(* y_1 1)` is what the naive generator gives. A generator that
also knows `n = 1` avoids it, and squaring halves the number of multiplications
for even `n`. Squaring needs the square's operand twice, so the generator
binds it with `genlet` instead of copying it:

```clojure klara-repl
k=> (def spower
      (fn [n x]
        (cond (= n 0) (code 1)
              (= n 1) x
              (even? n) (let [h (genlet (spower (quot n 2) x))]
                          (code (* (esc h) (esc h))))
              :else (code (* (esc x) (esc (spower (dec n) x)))))))
#'spower
k=> :repl/code (code (fn [y] (esc (spower 13 (code y)))))
(fn [y_1]
  (let [t_2 (* y_1 (* y_1 y_1)) t_3 (* t_2 t_2)] (* y_1 (* t_3 t_3))))
k=> ((run (code (fn [y] (esc (spower 13 (code y)))))) 2)
8192
```

Without `genlet`, the same generator duplicates the operand at every squaring,
and the code for `x^(2^k)` grows as `2^k`:

```clojure klara-repl
k=> (def dpower
      (fn [n x]
        (cond (= n 0) (code 1)
              (= n 1) x
              (even? n) (let [h (dpower (quot n 2) x)] (code (* (esc h) (esc h))))
              :else (code (* (esc x) (esc (dpower (dec n) x)))))))
#'dpower
k=> (code (fn [y] (esc (dpower 4 (code y)))))
(code (fn [y_1] (* (* y_1 y_1) (* y_1 y_1))))
k=> [(code-size (code (fn [y] (esc (dpower 64 (code y))))))
     (code-size (code (fn [y] (esc (spower 64 (code y))))))]
[128 24]
```

## What it demonstrates

- `code`, `esc` and `run`, and the split between present values (`n`) and
  future values (`y`).
- Fresh, readable binder names in generated code (`y_1`, `t_2`).
- Let-insertion (`genlet`) as the way to share a computation in generated code
  without duplicating it: `t_2` is `y^3`, `t_3` is `y^6`, and the result is
  `y * y^6 * y^6`. The binding is placed under `fn [y]`, the highest
  point where its free variable `y` is in scope.

## References

- A. P. Ershov, "On the partial computation principle", *Information
  Processing Letters* 6(2), 1977.
- W. Taha and T. Sheard, "Multi-stage programming with explicit annotations",
  PEPM 1997.
- O. Kiselyov, "The design and implementation of BER MetaOCaml", FLOPS 2014,
  LNCS 8475.
