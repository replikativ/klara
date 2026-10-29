# Example 6: specializing a regular expression matcher

Rob Pike's backtracking matcher (from Kernighan's chapter in *Beautiful Code*)
handles literals, `.`, `*`, `^` and `$` in about thirty lines of C. It
interprets the pattern on every call. Staging the matcher on a fixed pattern
turns it into a matcher *compiled* for that pattern: the pattern dispatch runs
at generation time, and the generated code only reads the text. This is the
"staged interpreter is a compiler" idea of example 4 applied to a classic.
The LMS tutorials use it in the same way.

## The interpreter

```clojure klara-repl
k=> (def matches?
      (fn [re s]
        (letfn [(here [re i]
                  (cond (empty? re) true
                        (= \* (second re)) (star (first re) (drop 2 re) i)
                        (and (= \$ (first re)) (empty? (rest re))) (= i (count s))
                        (< i (count s)) (and (or (= \. (first re)) (= (first re) (nth s i)))
                                             (here (rest re) (inc i)))
                        :else false))
                (star [c re i]
                  (cond (here re i) true
                        (and (< i (count s)) (or (= c \.) (= c (nth s i)))) (star c re (inc i))
                        :else false))]
          (let [re (seq re)]
            (if (= \^ (first re))
              (here (rest re) 0)
              (loop [i 0]
                (cond (here re i) true
                      (< i (count s)) (recur (inc i))
                      :else false)))))))
#'matches?
k=> [(matches? "ab*c" "xabbbc") (matches? "^ab*c$" "xabbc") (matches? "a.c" "zzabc")]
[true false true]
```

## The staged matcher

The pattern `re` is present. The text `s` is code. The position `i` is
*partially static*: a present number while the matcher is still at a fixed
offset from the start (after `^`, or before the first `*`), and code
once a `*` loop has consumed an unknown number of characters. `dyn` turns a
present position into code (by `lift`). `step` advances a position: it adds 1
at generation time, or let-binds `(inc j)` once with `genlet`.

```clojure klara-repl
k=> (def compile-re
      (fn [re]
        (letfn [(dyn [i] (if (code? i) i (lift i)))
                (step [i] (if (code? i) (genlet (code (inc (esc i)))) (inc i)))
                (test-char [c s i then]
                  (if (= c \.)
                    then
                    (code (if (= c (nth (esc s) (esc (dyn i)))) (esc then) false))))
                (here [re s i]
                  (cond (empty? re) (code true)
                        (= \* (second re)) (star (first re) (drop 2 re) s i)
                        (and (= \$ (first re)) (empty? (rest re)))
                        (code (= (esc (dyn i)) (count (esc s))))
                        :else (code (if (< (esc (dyn i)) (count (esc s)))
                                      (esc (test-char (first re) s i
                                                     (if (empty? (rest re))
                                                       (code true)
                                                       (here (rest re) s (step i)))))
                                      false))))
                (star [c re s i]
                  (code (loop [j (esc (dyn i))]
                          (if (esc (here re s (code j)))
                            true
                            (if (< j (count (esc s)))
                              (esc (test-char c s (code j) (code (recur (inc j)))))
                              false)))))]
          (let [re (seq re)]
            (code (fn [s]
                    (esc (if (= \^ (first re))
                           (here (rest re) (code s) 0)
                           (code (loop [i 0]
                                   (if (esc (here re (code s) (code i)))
                                     true
                                     (if (< i (count s)) (recur (inc i)) false))))))))))))
#'compile-re
```

## Compiled matchers

An anchored pattern compiles to fixed offsets until the `*`, and then to one
loop for the star:

```clojure klara-repl
k=> :repl/code (compile-re "^ab*c$")
(fn [s_1]
  (if (< 0 (count s_1))
    (if (= \a (nth s_1 0))
      (loop [j_2 1]
        (let [t_3 (inc j_2)]
          (if (if (< j_2 (count s_1))
                (if (= \c (nth s_1 j_2)) (= t_3 (count s_1)) false)
                false)
            true
            (if (< j_2 (count s_1))
              (if (= \b (nth s_1 j_2)) (recur (inc j_2)) false)
              false))))
      false)
    false))
```

An unanchored pattern tries every start position, and `.` costs only a bounds
check:

```clojure klara-repl
k=> :repl/code (compile-re "a.c")
(fn [s_1]
  (loop [i_2 0]
    (let [t_3 (inc i_2) t_4 (inc t_3)]
      (if (if (< i_2 (count s_1))
            (if (= \a (nth s_1 i_2))
              (if (< t_3 (count s_1))
                (if (< t_4 (count s_1))
                  (if (= \c (nth s_1 t_4)) true false)
                  false)
                false)
              false)
            false)
        true
        (if (< i_2 (count s_1)) (recur (inc i_2)) false)))))
```

The compiled matchers agree with the interpreter:

```clojure klara-repl
k=> (let [pats ["ab*c" "^ab*c$" "a.c" "^a*$" "x$"]
          texts ["xabbbc" "abbc" "zzabc" "aaa" "" "ax" "ac"]]
      (= (mapcat (fn [p] (map (fn [t] (matches? p t)) texts)) pats)
         (mapcat (fn [p] (map (run (compile-re p)) texts)) pats)))
true
```

## What it demonstrates

- Specializing an interpreter (the matcher) to its static input (the pattern):
  no pattern dispatch is left in the generated code.
- Partially static data. The position is a present number while it is known,
  and code after a `*`. Constant offsets fold away (`(nth s 0)`, `loop [j 1]`).
- `genlet` naming the advanced position once instead of nesting
  `(inc (inc i))`. The binding floats to the top of the generated loop body,
  the highest point where `j`/`i` is bound. This follows BER MetaOCaml's
  genlet. The binding is then computed on every iteration even when the
  guard fails, which is harmless only because `inc` is pure: let-insertion is
  for pure expressions.
- `recur` inside a code fragment built by a helper (`test-char`) and spliced
  into a generated `loop`. The recur target is the generated loop, as with any
  variable.

The generated code can grow exponentially in the number of `*`s, because
each star inlines the rest of the pattern inside its loop. `with-genletrec`
keyed by the pattern suffix would generate one function per suffix instead
(compare example 3). That variant is left out to keep the example small.

## References

- B. Kernighan, "A regular expression matcher", chapter 1 of A. Oram and
  G. Wilson (eds.), *Beautiful Code*, O'Reilly, 2007. The matcher is Rob
  Pike's.
- T. Rompf and M. Odersky, "Lightweight modular staging: a pragmatic approach
  to runtime code generation and compiled DSLs", GPCE 2010. The LMS tutorials
  (scala-lms.github.io) include a staged version of the same matcher.
- N. Amin and T. Rompf, "Collapsing towers of interpreters", POPL 2018. A
  staged interpreter is a compiler.
