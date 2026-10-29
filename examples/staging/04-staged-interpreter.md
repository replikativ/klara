# Example 4: a staged interpreter yields a compiler

The first Futamura projection: specializing an interpreter to a source program
gives a target program. With explicit staging, the specializer is the staged
interpreter itself. Amin and Rompf's Pink goes one step further: one evaluator
is *stage-polymorphic*. Its primitive operations either compute or generate
code, so the same definition serves as interpreter and as compiler, and towers
of interpreters collapse into one compiled program.

This example writes an evaluator for a tiny Lisp once, parameterized by its
operations. With one set of operations it interprets; with the other it
generates Klara code.

## The object language

Numbers, variables, `(+ a b)`, `(- a b)`, `(* a b)`, `(if c a b)`
(where 0 is false), single-argument recursive functions `(lambda f x body)`, and
application `(e1 e2)`. Programs are Klara data:

```clojure klara-repl
k=> (def fac-src '(lambda fac n (if n (* n (fac (- n 1))) 1)))
#'fac-src
```

## One evaluator, two stages

```clojure klara-repl
k=> (def evalp
      (fn [ops e env]
        (let [ev (fn [e] (evalp ops e env))]
          (cond
            (number? e) ((:lit ops) e)
            (symbol? e) (get env e)
            (= 'if (first e)) ((:if ops) (ev (nth e 1)) (fn [] (ev (nth e 2))) (fn [] (ev (nth e 3))))
            (= '+ (first e)) ((:add ops) (ev (nth e 1)) (ev (nth e 2)))
            (= '- (first e)) ((:sub ops) (ev (nth e 1)) (ev (nth e 2)))
            (= '* (first e)) ((:mul ops) (ev (nth e 1)) (ev (nth e 2)))
            (= 'lambda (first e))
            (let [f (nth e 1) x (nth e 2) body (nth e 3)]
              ((:fun ops) (fn [self arg] (evalp ops body (assoc env f self x arg)))))
            :else ((:app ops) (ev (first e)) (ev (second e)))))))
#'evalp
```

The interpreting operations compute:

```clojure klara-repl
k=> (def interp
      {:lit (fn [n] n)
       :add + :sub - :mul *
       :if (fn [c t e] (if (zero? c) (e) (t)))
       :fun (fn [body] (fn self [v] (body self v)))
       :app (fn [f a] (f a))})
#'interp
k=> (evalp interp (list fac-src 5) {})
120
```

The generating operations build code. Each one is the corresponding
interpreting operation inside `code`, with `esc` on the parts the evaluator
supplies. `:lit` lifts a present number. `:fun` generates a `fn` and evaluates
the body with the code of its binders in the environment.

```clojure klara-repl
k=> (def gen
      {:lit (fn [n] (lift n))
       :add (fn [a b] (code (+ (esc a) (esc b))))
       :sub (fn [a b] (code (- (esc a) (esc b))))
       :mul (fn [a b] (code (* (esc a) (esc b))))
       :if (fn [c t e] (code (if (zero? (esc c)) (esc (e)) (esc (t)))))
       :fun (fn [body] (code (fn self [v] (esc (body (code self) (code v))))))
       :app (fn [f a] (code ((esc f) (esc a))))})
#'gen
```

## Compiling

Specializing the evaluator to `fac-src` with the generating operations is
compilation:

```clojure klara-repl
k=> :repl/code (evalp gen fac-src {})
(fn self_1 [v_2] (if (zero? v_2) 1 (* v_2 (self_1 (- v_2 1)))))
k=> (def fac (run (evalp gen fac-src {})))
#'fac
k=> (fac 5)
120
```

The residual program has no trace of the interpreter. There is no dispatch on
the shape of `e`, no environment map, no `ops` lookup, and the object-language
variables became Klara binders. That is the meaning of "no interpretive
overhead" for the displayed residual. Sharing the evaluator keeps its traversal
in one definition: a fix to `evalp` is made once. Agreement of interpretation
and generated execution additionally requires a relation between the operation
sets, preserved by the evaluator and its generated binders. That general
correspondence has not been proved for this example; sharing the evaluator
alone does not establish it; see the stage-polymorphic generator obligation
in the [correctness ledger](../../doc/engineering/correctness.md).

A program with free variables of the object language compiles to open code
only when the environment supplies code for them:

```clojure klara-repl
k=> (code (fn [k] (esc (evalp gen '(* k (+ 1 2)) {'k (code k)}))))
(code (fn [k_1] (* k_1 (+ 1 2))))
```

## Towers

Pink collapses towers of interpreters of *arbitrary* height: an interpreter
written in Pink, running another interpreter, running a user program, compiles
to one program with no interpretive overhead at any level. This works because
Pink's evaluator is written in Pink, and its `lift` operator is part of the
object language, so every level of the tower can be stage-polymorphic. The
tiny Lisp here has only numbers, so it cannot express an interpreter, and the
example stops at the base case: one level of interpretation, removed by one
level of staging. A Klara evaluator for a language with lists and quotation,
with `lift` exposed to the object language, would be the next step.

## What it demonstrates

- The first Futamura projection with explicit staging. `(evalp gen p {})` is a
  compiler from the tiny Lisp to Klara.
- Stage polymorphism. One evaluator is used with two operation sets, and the
  generating set is the interpreting set under `code`/`esc`.
- Generated recursive functions (`fn self`). Object-language binders become
  fresh Klara binders.

## References

- N. Amin and T. Rompf, "Collapsing towers of interpreters", *Proc. ACM
  Program. Lang.* 2(POPL), Article 33, 2018.
- Y. Futamura, "Partial evaluation of computation process — an approach to a
  compiler-compiler", *Systems, Computers, Controls* 2(5), 1971; reprinted in
  *Higher-Order and Symbolic Computation* 12(4), 1999.
- N. D. Jones, C. K. Gomard and P. Sestoft, *Partial Evaluation and Automatic
  Program Generation*, Prentice Hall, 1993.
