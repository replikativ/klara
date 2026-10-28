# 5. Staging: code values

A staged program runs in two steps. The first step knows part of the input
and **generates code** specialized to it, and the second step runs that code
on the rest of the input. Klara supports this the way MetaOCaml does: code is a
value you build with brackets, splice with escapes, and run when it is closed.
A dynamic check refuses code that mentions a variable outside its binder.

This chapter covers the four forms (`code`, `esc`, `run`, `lift`),
let-insertion (`genlet`, `with-genletrec`), and the scope-extrusion check. The
worked examples are in `examples/staging/`. The design is
`doc/background/01-core-v2.md` §6 and research note
`doc/background/research/C-staging.md`. The implementation notes are
`doc/background/impl/S4.md`.

## Syntax

| Form | Meaning | MetaOCaml |
|---|---|---|
| `(code e)` | the code of `e`, not evaluated: a code value | `.< e >.` |
| `(esc e)` | inside `code`: evaluate `e` now and splice the code value it returns | `.~e` |
| `(run c)` | compile and evaluate closed code `c` under the current basis | `Runcode.run` |
| `(lift v)` | the code that rebuilds the present value `v` | `Lifts`, CSP |
| `(genlet c)` | let-bind `c` at the highest enclosing let-insertion point; returns the code of the variable | `genlet` |
| `(with-genletrec [g] body)` | a locus for a generated `letfn` group; `(g gen key)` memoizes generated functions | `with_locus_rec`, `mkgenlet` |

Clojure's backquote keeps its Clojure meaning. `` `(+ 1 x) `` is syntax-quote
and produces a list, which is data, not code. Code values are built only with
`code`.

Some helpers work on code values: `(code? x)`, `(closed? c)` (no free
variables), `(code-size c)` (the number of nodes, used to compare generators),
and `(code-vector cs)` (the code of a vector of code values whose number is
known only at generation time).

REPL support: the printer shows a code value as `(code <Klara source>)`, and
`:code <form>` pretty-prints the source of the code value that `<form>`
evaluates to.

## Code, escape, run

```klara-repl
k=> (code (+ 1 2))
(code (+ 1 2))
k=> (run (code (+ 1 2)))
3
k=> (def power
      (fn [n x]
        (if (zero? n)
          (code 1)
          (code (* (esc x) (esc (power (dec n) x)))))))
#'power
k=> (code (fn [y] (esc (power 3 (code y)))))
(code (fn [y_1] (* y_1 (* y_1 (* y_1 1)))))
k=> ((run (code (fn [y] (esc (power 3 (code y)))))) 2)
8
```

**Meaning.** `code` raises the stage. Its body is not evaluated but *built*,
and the result is a value holding a term. Inside the body, `esc` lowers the
stage again. Its argument is evaluated at once, to a code value, and that term
is spliced in place. A binder inside `code` (the `fn [y]` above) gets a
**fresh name** each time the code is built, so a spliced term can never
capture or be captured by a binder it did not mention (hygiene). The printer
renames fresh names to `base_n` in order of appearance, so the printed source
does not depend on what was generated before.

A variable of generated code that is used from the present stage, as in
`(esc y)` under `fn [y]`, stands for its own code: `(esc y)` and
`(esc (code y))` are the same.

```klara-repl
k=> (code (fn [z] (+ z (esc z))))
(code (fn [z_1] (+ z_1 z_1)))
```

`run` turns closed code into a core term, the de Bruijn form of
`doc/semantics.md` §1, and evaluates it under the **current basis**: world
names in generated code resolve in the world that runs it, like any other
code.

```klara-repl
k=> (def sq (fn [x] (* x x)))
#'sq
k=> (run (code (sq 7)))
49
```

There is no reduction rule for `code` and `esc` in the formal spec yet
(`doc/semantics.md` §1 lists them as T0 extensions). Informally, the relation
to the spec is the following. A code value is a term with names. `run`
accepts it only when it is closed, which is exactly the precondition `WS 0 t`
under which the spec proves preservation and safety (`doc/semantics.md` §6).
A program that never runs open code therefore never reaches the spec's only
unnamed failure, `scope`. The relation to `specialize` is the s-m-n law.
`(specialize f a)` means `(fn [y] (f a y))`. A staged generator such as
`(fn [a] (code (fn [y] (esc (f-gen a (code y))))))` computes a residual that
agrees with it on value arguments, which is obligation O1 of
`research/C-staging.md`. The law holds at values only: `doc/semantics.md` §5
explains why an effectful argument breaks it.

## Levels

`code` nests. The code of code is a value too, and `esc` inside a nested
bracket splices at the level just outside it:

```klara-repl
k=> (code (code (+ 1 (esc (esc (code 2))))))
(code (code (+ 1 (esc 2))))
k=> (run (run (code (code (+ 1 2)))))
3
```

`esc` outside any `code` is an expansion error, and splicing something that is
not code is a stage error:

```klara-repl
k=> (esc 1)
!! expand: esc outside code
k=> (code (+ 1 (esc 2)))
!! stage: esc expects a code value, got 2
```

## lift: present values in generated code

A present value used inside `code` is **lifted**: generated code gets a
literal that rebuilds it. This is cross-stage persistence. `lift` does the
same explicitly.

```klara-repl
k=> (let [n 5] (code (+ n 1)))
(code (+ 5 1))
k=> (lift [1 :a "s" {:b 2}])
(code [1 :a "s" {:b 2}])
k=> (let [k 2 f (fn [z] (* z k))] (code (f 3)))
(code ((fn [z_1] (* z_1 2)) 3))
```

Numbers, strings, keywords, symbols, characters and persistent collections of
them become literals. A closure becomes its code, with its captured values
lifted in turn. A partial application becomes `specialize`. Host functions
such as `clojure.core/inc`, and closures that refer to themselves, cannot be
written as source, so they persist as opaque constants (printed `#<csp …>`).

`lift` **refuses** values that hold resources, following
`01-core-v2.md` §6 ("`lift` refuses authority-holding values"): atoms and
other mutable host objects, handler instances, continuations, genletrec
generators, and closures over any of them. Code values are refused too. A
code value goes into code with `esc`, not by lifting.

```klara-repl
k=> (lift (atom 0))
!! lift: cannot lift a value holding a resource (Atom); only data and functions over data persist into code
k=> (handle [h {:op (fn [k] (k 1))}] (lift h))
!! lift: cannot lift a value holding a resource (a handler instance); only data and functions over data persist into code
k=> (let [c (code 1)] (code (+ 1 c)))
!! stage: a code value is used inside code without esc
```

Authorities in the sense of RFC 0001 are not implemented yet. Today "resource"
means a host object that is not data, plus the Klara values that stand for
control (instances, continuations).

## Scope extrusion

Open code, meaning code with free variables, is legitimate while it is being
built: `(code y)` under `fn [y]` is open. It becomes wrong if it leaves the
extent of the code generation that binds its variables and is spliced or run
somewhere else. Klara checks this dynamically, as BER MetaOCaml does. A
generated variable is **alive** while the construction of its binder is still
on the continuation. Splicing code that mentions a dead variable is an error,
and so is running code with any free variable.

The classic counterexample stores open code in a mutable cell and splices it
later:

```klara-repl
k=> (let [r (atom nil)]
      (code (fn [x] (esc (do (reset! r (code x)) (code x)))))
      (code (fn [y] (esc @r))))
!! scope-extrusion: code mentions x, whose binder is not in scope where it is spliced (a variable escaped the code that binds it)
k=> (let [r (atom nil)]
      (code (fn [x] (esc (do (reset! r (code x)) (code x)))))
      (run @r))
!! scope-extrusion: code mentions x, whose binder is not in scope where the code is run (a variable escaped the code that binds it)
```

Open code that stays within its binder's extent may travel through any number
of helper functions:

```klara-repl
k=> (let [wrap (fn [c] (code (fn [y] (+ y (esc c)))))]
      (code (fn [x] (esc (wrap (code x))))))
(code (fn [x_1] (fn [y_2] (+ y_2 x_1))))
```

The check also works across host higher-order functions. A Klara closure
passed to `reduce` or `map` runs in a nested machine, and the check consults
the continuations suspended behind those host frames:

```klara-repl
k=> (code (fn [x] (esc (reduce (fn [acc i] (code (+ (esc acc) (* x i))))
                               (code 0) [1 2 3]))))
(code (fn [x_1] (+ (+ (+ 0 (* x_1 1)) (* x_1 2)) (* x_1 3))))
```

## Let-insertion

Splicing the same code value twice duplicates the computation it describes.
`genlet` binds it instead. It inserts `(let [t <code>] ...)` at the **highest
let-insertion point** where every free variable of the code is still bound,
and returns the code of `t`. Let-insertion points are the top of every `code`
bracket and the body of every binder in generated code. The placement follows
BER MetaOCaml's `genlet` (`ber-metaocaml-153/test/genlet.ml`):

```klara-repl
k=> (code (fn [x] (+ x (esc (genlet (code (+ 1 2)))))))
(code (let [t_1 (+ 1 2)] (fn [x_2] (+ x_2 t_1))))
k=> (code (fn [x] (+ x (esc (genlet (code (+ x 1)))))))
(code (fn [x_1] (let [t_2 (+ x_1 1)] (+ x_1 t_2))))
k=> (code (fn [x] (+ x (esc (genlet (code x))))))
(code (fn [x_1] (+ x_1 x_1)))
```

The closed expression floats out of the `fn`. The one that mentions `x` stops
just inside `fn [x]`. A variable or a constant is not bound at all. Because a
binding may float above conditionals and functions, it is evaluated even on
paths that do not use it: let-insertion is for pure, cheap-to-evaluate-early
expressions. A let-inserted name is alive as long as its insertion point is,
and the scope check covers it. `genlet` outside any `code` returns its argument
unchanged.

`genlet` is the ambient operation `:stage/genlet`, so a dynamic handler can
observe or replace it. This one disables let-insertion:

```klara-repl
k=> (handle :dynamic {:stage/genlet (fn [c k] (k c))}
      (code (fn [x] (+ x (esc (genlet (code (+ 1 2))))))))
(code (fn [x_1] (+ x_1 (+ 1 2))))
```

`with-genletrec` generates *recursive* bindings: a `letfn` group whose size
is decided at generation time. Inside `(with-genletrec [g] body)`, the call
`(g gen key)` returns the code of the function generated for `key`. It calls
`(gen key)` the first time it sees `key` and reuses the result after that. The
body must produce code, and the result is that code wrapped in the `letfn` of
all generated functions:

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

This is Ackermann's function specialized to `m = 2`. Without the memo table
the generator would unfold `(g gen m)` forever. Examples 1 and 3 in
`examples/staging/` measure code size with and without let-insertion.

## Worked examples

| Example | Shows |
|---|---|
| [1. power](../../examples/staging/01-power.md) | the residual `(fn [y] (* y ...))`; squaring with `genlet` |
| [2. matrix-vector](../../examples/staging/02-matrix-vector.md) | unrolling, dropping zeros, memoized let-insertion |
| [3. fib / gibonacci](../../examples/staging/03-fib-let-insertion.md) | duplication vs `genlet` vs `with-genletrec`, by code size |
| [4. staged interpreter](../../examples/staging/04-staged-interpreter.md) | first Futamura projection, a stage-polymorphic evaluator |
| [5. stream fusion](../../examples/staging/05-stream-fusion.md) | strymonas-style pipelines generating one loop; relation to S3 |
| [6. regex](../../examples/staging/06-regex.md) | a backtracking matcher specialized to a pattern |

## Not yet implemented

- **No formal rules.** `code`/`esc` are not in the ansatz spec. The
  scope-extrusion check is a dynamic check in T0, not a theorem.
- **No typed staging.** Nothing rejects ill-staged programs before they run.
  Errors are dynamic (`!! stage`, `!! scope-extrusion`).
- **Let-insertion and multi-shot continuations.** Insertion points hold their
  bindings in a mutable cell. Resuming a continuation twice inside one code
  bracket accumulates the bindings of both runs.
- **No authority accounting in `lift`.** "Resource" is approximated by
  "non-data host object or control value" until RFC 0001 is implemented.
- **No syntax values or `quote-syntax`.** Macros still receive plain data.
  Code values are a separate kind and are not macro input.
- **Run uses T0.** `run` evaluates generated code in the reference
  interpreter. Compiling it to a host function (or to C, via the planned K3
  back end) is future work, and so is installing generated code in the
  specialization cache of chapter 6.
