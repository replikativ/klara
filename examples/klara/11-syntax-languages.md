# 11. A binding extension with a reusable grammar

A small binding notation illustrates RFC 0006 LG1/LG2. The `binding-pair`
class validates a name and expands its initializer in the caller's context.
The body stays unexpanded until `let*` introduces the binding. Reusing the
class records a world value read; editing it invalidates consumers.

```clojure klara-repl
k=> (defsyntax-class binding-pair [[name :binding] [value :expr]])
#'binding-pair
k=> (defsyntax with-binding [[b :binding-pair] [body :body ...]]
      (qq (let* [~(syntax-attribute b 'name) ~(syntax-attribute b 'value)]
            ~@body)))
#'with-binding
k=> (with-binding [x 4] (with-binding [y (+ x 1)] (* x y)))
20
k=> (defsyntax saved [[e :expr]] (qq (let* [tmp 100] ~e)))
#'saved
k=> (let [tmp 7] (saved (with-binding [x tmp] (+ x tmp))))
14
k=> (defsyntax checked [[e :body]] (local-expand e))
#'checked
k=> (with-binding [x 3] (checked (+ x 2)))
5
```

`with-binding` composes with `saved` without capturing the caller's `tmp`.
`checked` preserves `x` through local expansion. All generated terms execute
in T0; this syntax layer adds no evaluator or compiler tier. See
[guide chapter 2](../../doc/guide/02-world.md#syntax-values-and-grammars-s13)
for optional/repeated patterns, definition contexts and the remaining limits.
