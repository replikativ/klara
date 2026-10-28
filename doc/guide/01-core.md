# 1. The core: values, functions, twelve forms

Klara reads Clojure syntax. Every program is expanded into **Klara Core**,
twelve forms with a small-step semantics (`doc/semantics.md`). This chapter
shows the values, the functions and the forms, and how familiar Clojure
syntax expands into the core.

## Values

Literals are Clojure data: numbers (including ratios), strings, keywords,
symbols, `nil`, booleans, and the persistent collections. Klara values have
no observable identity; equality is Clojure's `=`. (A bare keyword at the
prompt is a REPL command such as `:repl/help`, so keywords appear inside other
forms here.)

```klara-repl
k=> 42
42
k=> 1/3
1/3
k=> "text"
"text"
k=> [:key 'sym]
[:key sym]
k=> [1 2 (+ 1 2)]
[1 2 3]
k=> {:a 1 :b [true nil]}
{:a 1, :b [true nil]}
k=> (= [1 2] '(1 2))
true
```

A collection whose elements are all constants is a `quote` of a datum. A
collection with computed elements becomes a primitive call: `[1 2 (+ 1 2)]`
is `(prim vector 1 2 (prim + 1 2))`.

**Meaning.** Rule `prim` in `doc/semantics.md` §3: a primitive applied to
values reduces to its result. Klara's 44 primitives (`+`, `first`, `assoc`,
…) carry clojure.core names and, by the naming rule, behave like the
clojure.core functions of the same name on programs that do not fail.

## Functions

`fn` makes a closure: code plus the values of the locals it captured.
Application is call-by-value, left to right.

```klara-repl
k=> ((fn [x y] (- x y)) 10 3)
7
k=> (let [make-adder (fn [n] (fn [x] (+ x n)))
          add2 (make-adder 2)]
      (add2 40))
42
k=> ((fn [& xs] (vec xs)) 1 2 3)
[1 2 3]
```

**Meaning.** Rule β: `((fn [x] b) v)` reduces to `b` with `v` substituted
for `x`. The spec has unary functions only and curries; T0 implements n-ary
functions with an optional rest parameter directly. Applying a number is the
named stuck state `notFn`; T0 raises it as an error:

```klara-repl
k=> (1 2)
!! eval: not a function
k=> ((fn [x] x) 1 2)
!! eval: arity mismatch
```

A Klara closure is also a Clojure function, so clojure.core's higher-order
functions accept it:

```klara-repl
k=> (reduce (fn [acc x] (+ acc (* x x))) 0 [1 2 3])
14
k=> (mapv (fn [x] (inc x)) [1 2 3])
[2 3 4]
```

## Recursion and loops

`letfn`, `loop`/`recur` and named `fn`s expand to `letrec`. Self and mutual
tail calls run in constant space, although the JVM has no general tail
calls (the machine pushes no frame for a call in tail position).

```klara-repl
k=> (loop [i 0 acc 0] (if (< i 100000) (recur (inc i) (+ acc i)) acc))
4999950000
k=> (letfn [(ev? [n] (if (zero? n) true (od? (dec n))))
            (od? [n] (if (zero? n) false (ev? (dec n))))]
      [(ev? 10000) (ev? 10001)])
[true false]
k=> ((fn count-up [i] (if (< i 50000) (count-up (inc i)) i)) 0)
50000
```

**Meaning.** Rules `letrec` and β-fix: `letrec` makes a recursive closure
`fix fb`; applying it substitutes the closure for its own name and the
argument for the parameter.

Top-level definitions can also recurse through the world, by name
(chapter 2):

```klara-repl
k=> (defn fact [n] (if (zero? n) 1 (* n (fact (dec n)))))
#'fact
k=> (fact 20)
2432902008176640000
```

## The twelve forms

| # | Form | Surface | What it does |
|---|---|---|---|
| 1 | local | `x` | a bound variable (a de Bruijn index in the core) |
| 2 | quote | `'d`, literals | a datum |
| 3 | fn | `(fn [x ..] e)` | a closure |
| 4 | application | `(f a ..)` | call a function |
| 5 | let | `(let [x e] b)` | bind one value |
| 6 | if | `(if c t e)` | branch on Clojure truthiness (`nil` and `false` are false) |
| 7 | letrec | via `letfn`, `loop`, named `fn` | recursive functions |
| 8 | resolve | a world name | read a definition from the basis (chapter 2) |
| 9 | prim | `(+ a b)`, or explicitly `(prim + a b)` | a portable primitive operation |
| 10 | perform | `(perform h :op a ..)`, `(perform :ns/op a ..)` | perform an effect (chapter 3) |
| 11 | handle | `(handle [h {:op f ..}] body)`, `(handle :dynamic {..} body)` | install a handler (chapter 3) |
| 12 | specialize | `(specialize f a ..)` | s-m-n: fix some arguments (below) |

Both T0 and the formal spec add `code` and `esc` for staging, covered in
chapter 5. Since S5 the spec also models `run_` (T0 uses `:stage/run`),
including dynamic scope-extrusion checks and scoping preservation.

```klara-repl
k=> (prim + 1 2)
3
k=> (if nil :then :else)
:else
k=> (if 0 :then :else)
:then
```

### `specialize`

`(specialize f a)` is a function of the remaining arguments. Its
*reference meaning* is partial application; a real specializer may return
faster code, but it must agree with that meaning (the s-m-n law,
`doc/semantics.md` §5, proved in the spec for values).

```klara-repl
k=> ((specialize (fn [a b] (- a b)) 10) 3)
7
k=> (= ((specialize (fn [a b c] [a b c]) 1 2) 3) ((fn [a b c] [a b c]) 1 2 3))
true
```

## How Clojure syntax expands

The expander turns every surface form into core terms. It is hygienic
(scope sets), resolves locals to de Bruijn indices and records what it read
from the world. The REPL command `:repl/expand` shows the core term of a form,
printed back as Klara source (locals get numbered names):

```klara-repl
k=> :repl/expand (let [x 1] (when (pos? x) :yes))
(let [x_1 1] (if (pos? x_1) :yes))
k=> :repl/expand (loop [i 0] (if (< i 3) (recur (inc i)) i))
(let [i_1 0] (letfn [(loop_2 [i_3] (if (< i_3 3) (loop_2 (inc i_3)) i_3))] (loop_2 i_1)))
k=> :repl/expand (try (/ 1 0) (catch ArithmeticException e :div0))
(handle :dynamic #:exn{:raise (fn [ex_1 k_2] (if (instance? (perform :host/class (quote ArithmeticException)) ex_1) (let [e_3 ex_1] :div0) (throw ex_1)))} (/ 1 0))
```

`when` is a clojure.core macro: the expander runs it (with hygiene) and
expands its output, an `if`. `loop` became a `letfn` (a `letrec`) applied to
the initial value. `try` became a dynamic handler of `:exn/raise`.

The term itself is data. Calling the expander directly shows it raw:

```klara-repl
k=> (klara.expand/expand-expr '(fn [a b] (- a b)) klara.world/empty-root)
{:op :fn, :arity 2, :rest? false, :body {:op :prim, :name -, :args [{:op :local, :index 1} {:op :local, :index 0}]}}
k=> (klara.expand/expand-expr '(map inc [1 2]) klara.world/empty-root)
{:op :perform, :target nil, :name :host/call, :args [{:op :quote, :datum clojure.core/map} {:op :perform, :target nil, :name :host/var, :args [{:op :quote, :datum clojure.core/inc}]} {:op :quote, :datum [1 2]}]}
```

In the first term, `b` is index 0 and `a` index 1: binders are pushed left
to right, so the last parameter is innermost. The second shows what the
printer of `:repl/expand` resugars: a call of a clojure.core function is an
ambient effect, `(perform :host/call 'clojure.core/map ..)`.

| Surface | Core |
|---|---|
| `(let [a 1 b 2] e)` | nested single `let`s |
| `(do e1 e2)` | `(let [_ e1] e2)` with a hidden binder |
| `loop`/`recur` | a `letrec` of a one-parameter-list fn, applied to the initial values |
| named `fn`, `letfn` | `letrec` |
| `(throw e)` | `(perform :exn/raise e)` |
| `(try .. (catch C e ..))` | a dynamic handler of `:exn/raise` that tests the classes in order and re-raises otherwise |
| `when`, `cond`, `and`, `or`, `->`, `defn`, … | the clojure.core macro, run by the expander |
| `(map f xs)` and other clojure.core functions | `(perform :host/call 'clojure.core/map f xs)` |
| `[a (f b)]`, `{k (f v)}`, `#{..}` with computed elements | `(prim vector ..)`, `(prim hash-map ..)`, `(prim hash-set ..)` |

Calls to clojure.core functions are **ambient effects** (`:host/call`,
`:host/var`), answered by a reference handler that calls the real
function. That keeps the host visible in the core: a dynamic handler can
intercept host calls (chapter 7).

### Code identity

Because locals are indices, α-equivalent programs are equal terms. The
**CodeId** of a term is the SHA-256 of its canonical form, so renaming a
parameter does not change it:

```klara-repl
k=> (= (klara.core/code-id (klara.expand/expand-expr '(fn [a] (* a a)) klara.world/empty-root))
       (klara.core/code-id (klara.expand/expand-expr '(fn [b] (* b b)) klara.world/empty-root)))
true
```

The CodeId is the key for everything that caches: definitions (chapter 2),
executables and certificates (chapter 6).

## Not yet supported

S1's expander covers a working subset of Clojure. Missing: multi-arity
`fn`/`defn`, `finally`, Java interop with `.` and `new`, `case*`, `set!`,
`var` and metadata. `recur` is not checked for tail position. An unknown
name is an expansion error, as in Clojure:

```klara-repl
k=> (car [1 2])
!! expand: unable to resolve car
```
