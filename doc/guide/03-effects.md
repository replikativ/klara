# 3. Effects and handlers

Inference (`choose`/`observe`), generators, state, exceptions, world access
and host calls are all **effects** in Klara: a program *performs* an
operation, and a *handler* decides what it means. This chapter covers the
two forms involved, `perform` and `handle`, the two kinds of handler, and
the standard patterns built from them.

The design is RFC 0002 (`rfc/0002-effects-and-handlers.md`); the rules are
in `doc/semantics.md` §3 and §7.

## perform and handle

```klara-repl
k=> (handle [h {:ask (fn [x k] (k (* 10 x)))}]
      (+ 1 (perform h :ask 4)))
41
```

`(handle [h clauses] body)` creates a fresh **handler instance**, binds it to
`h` in `body` and runs `body`. `(perform h :ask 4)` performs the operation
`:ask` with argument `4` on that instance. The clause for `:ask` receives
the arguments and the **continuation** `k`: the rest of the computation from
the `perform` up to the `handle`, as a function. Calling `(k v)` resumes the
body with `v` as the value of the `perform`.

**Meaning.** Rule `Handle` allocates a fresh label `l` and replaces `h` by
the capability `cap l`. Rule `Op` fires when the body reaches
`E[perform :ask (cap l) v]` with no other instance `l` in between: the clause
runs with `k = (fn [y] (handling l E[y] ...))`. Since `k` reinstalls the
handler around `E`, handlers are **deep**: later performs in the resumed
computation are handled by the same instance.

A clause decides how often to resume:

| The clause … | Pattern | Examples |
|---|---|---|
| calls `k` once, as its last act | tail-resumptive | state, reader, logging, weight accumulation |
| never calls `k` | abortive | exceptions, early exit, suspension |
| calls `k` several times | multi-shot | enumeration, backtracking, particle resampling |

```klara-repl
k=> (handle [e {:stop (fn [k] :aborted)}]
      (+ 1 (perform e :stop)))
:aborted
k=> (handle [c {:tick (fn [k] (+ 1 (k nil))) :return (fn [_] 0)}]
      (perform c :tick) (perform c :tick) (perform c :tick))
3
```

The optional `:return` clause transforms the body's final value. In the
second example it maps the body's result to 0, and each `:tick` adds one
around the resumed rest: the handler counts the ticks.

## State, generators, enumeration

**State** is a handler whose clauses return functions of the current store
(state-passing style):

```klara-repl
k=> ((handle [st {:get    (fn [k] (fn [s] ((k s) s)))
                  :put    (fn [v k] (fn [s] ((k nil) v)))
                  :return (fn [x] (fn [s] [x s]))}]
       (perform st :put (+ 1 (perform st :get)))
       (perform st :get))
     41)
[42 42]
```

A **generator** yields values to its handler. Here the handler collects
them:

```klara-repl
k=> (handle [g {:yield  (fn [v k] (let [[vs r] (k nil)] [(cons v vs) r]))
                :return (fn [r] [() r])}]
      (perform g :yield 1) (perform g :yield 2) (perform g :yield 3)
      :done)
[(1 2 3) :done]
```

A handler that does *not* resume turns the running generator into a value
that can be resumed later; `examples/klara/09-basis-raise.md` drives a
simulation this way.

**Multi-shot** resumption enumerates. Calling `k` twice runs the rest of the
computation for both answers:

```klara-repl
k=> (handle [amb {:flip (fn [k] (concat (k true) (k false))) :return (fn [x] [x])}]
      [(perform amb :flip) (perform amb :flip)])
([true true] [true false] [false true] [false false])
```

## choose and observe

Probabilistic programs perform `:choose` and `:observe`. They are ordinary
user operations; the inference algorithm is the handler. The model below
flips two coins and observes that at least one came up heads.

```klara-repl
k=> (defn two-coins [m]
      (let [a (perform m :choose 1/2)
            b (perform m :choose 1/2)]
        (perform m :observe (if (or a b) 1 0))
        [a b]))
#'two-coins
```

**Exact enumeration** resumes `:choose` with both values and multiplies the
probabilities along each path. `:observe` with likelihood `w` scales the
weight; the result is the unnormalized posterior as a list of
`[weight value]` pairs.

```klara-repl
k=> (defn enumerate [model]
      ((handle [m {:choose  (fn [p k] (fn [w] (concat ((k true) (* w p))
                                                    ((k false) (* w (- 1 p))))))
                   :observe (fn [lik k] (fn [w] ((k nil) (* w lik))))
                   :return  (fn [x] (fn [w] (if (zero? w) [] [[w x]])))}]
         (model m))
       1))
#'enumerate
k=> (enumerate two-coins)
([1/4 [true true]] [1/4 [true false]] [1/4 [false true]])
k=> (let [ps (enumerate two-coins)
          z (reduce + (map first ps))]
      (into {} (map (fn [[w x]] [x (/ w z)]) ps)))
{[true true] 1/3, [true false] 1/3, [false true] 1/3}
```

The same model runs unchanged under a sequential Monte Carlo handler with
resampling in `examples/klara/07-smc.md`.

## Lexical instances: no accidental handling

`perform` names the instance it targets. An inner handler for the same
operation does not intercept it:

```klara-repl
k=> (handle [outer {:ask (fn [x k] (k [:outer-saw x]))}]
      (handle [inner {:ask (fn [x k] (k [:inner-saw x]))}]
        [(perform outer :ask 1) (perform inner :ask 2)]))
[[:outer-saw 1] [:inner-saw 2]]
```

With dynamic handlers only, a library that installs its own `:ask` handler
between your handler and your code would silently capture your operations.
Lexical instances rule this out (obligation EF4, tested in
`test/klara/eval_test.clj`).

An instance is valid only inside its `handle`. Performing on it after the
`handle` has returned is the spec's *unhandled instance* state:

```klara-repl
k=> (let [h (handle [h {:op (fn [k] (k 1))}] h)]
      (perform h :op))
!! unhandled: unhandled lexical effect :op (instance out of extent, or behind a host frame)
```

## Ambient effects and dynamic handlers

Some effects belong to the platform rather than to the program: world
access (`:world/*`), host interop (`:host/*`), exceptions (`:exn/*`) and
time (`:time/*`, not implemented yet). They are performed without an
instance, `(perform :ns/op args..)`, and found by **dynamic** search for the
nearest `(handle :dynamic {..} ..)` with a clause for the operation. If
there is none, the operation's **reference handler** answers.

```klara-repl
k=> (perform :world/version)
2
k=> (handle :dynamic {:host/call (fn [sym & args] ((last args) [:mocked sym]))}
      (slurp "/nonexistent"))
[:mocked clojure.core/slurp]
```

`slurp` is a clojure.core function, so the expander turned the call into
`(perform :host/call 'clojure.core/slurp "/nonexistent")`. The dynamic
handler intercepted it before the reference handler could touch the file
system. (The continuation is the last argument of a clause.)

The two kinds are kept apart by a well-formedness check: a lexical handler
may only handle user operations, a dynamic one only ambient operations, and
a user operation must name its instance.

```klara-repl
k=> (handle [h {:host/call (fn [& args] 0)}] 1)
!! eval: ill-formed term
k=> (perform :my/op 1)
!! eval: ill-formed term
```

Both terms are rejected by the core's well-formedness check before they
run; `klara.core/wf-errors` lists the reasons ("lexical handlers handle
user ops only", "untargeted perform of non-ambient op :my/op").

## Exceptions

`throw` performs `:exn/raise`; `try`/`catch` installs a dynamic handler for
it. Host exceptions thrown by primitives or host calls become `:exn/raise`
at the call site, so they are caught the same way.

```klara-repl
k=> (try (throw (ex-info "boom" {:x 1})) (catch Exception e (ex-data e)))
{:x 1}
k=> (try (/ 1 0) (catch ArithmeticException e :div0))
:div0
k=> (try (try (/ 1 0) (catch clojure.lang.ExceptionInfo e :inner))
         (catch ArithmeticException e :outer))
:outer
k=> (throw (ex-info "uncaught" {:x 2}))
!! ex-info: uncaught
```

An exception nobody catches leaves the machine as a host exception. The
dynamic `:exn/raise` handler of a `try` never sees lexical effects:

```klara-repl
k=> (handle [h {:op (fn [k] (k 1))}]
      (try (perform h :op) (catch Exception e :wrong)))
1
```

## The host boundary

A Klara closure passed to a Clojure function (for example `map`) is called
by host code and runs in a nested machine. A perform inside it that targets
a handler *outside* the host call cannot reach it: the JVM frames of `map`
lie in between, and they cannot be captured. Klara reports this as an error
instead of misbehaving (obligation EF5):

```klara-repl
k=> (handle [h {:op (fn [k] (k 1))}]
      (vec (map (fn [x] (perform h :op)) [1 2])))
!! unhandled: unhandled lexical effect :op (instance out of extent, or behind a host frame)
```

Exceptions do cross the boundary, and a handler *inside* the callback works
normally (example 7 relies on this).

## Not yet implemented

- **Operation classes.** RFC 0002 classifies each operation as
  tail-resumptive, abortive or general at definition time, so that the
  compiler can turn the first two into direct calls and confine
  continuation capture to narrow regions. T0 captures continuations for
  every perform; there is no `defeffect` declaration yet.
- **Dispatch erasure** by specializing a region per handler context.
- **The authority restriction on multi-shot resumption** (RFC 0001): a
  continuation that holds a resource should not be resumed twice. T0 does
  not check it.
- `:time/*` operations, `finally`.
