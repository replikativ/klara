# 7. Clojure interop

Klara is embedded in the Clojure ecosystem: it reads Clojure syntax, uses
Clojure's data structures (for now), calls Clojure functions and Java
statics, and Klara closures are Clojure functions. This chapter explains
the two ways Clojure code can take part in a Klara program, the rule that
keeps shared names honest, and the host quirks Klara tolerates but does not
adopt.

## Calling Clojure and Java

A clojure.core function is called like in Clojure. Qualified names reach
any loaded Clojure namespace, and `Class/member` reaches Java statics:

```klara-repl
k=> (clojure.string/upper-case "abc")
"ABC"
k=> (Math/sqrt 2.0)
1.4142135623730951
k=> Long/MAX_VALUE
9223372036854775807
k=> (sort-by (fn [x] (- x)) [3 1 2])
(3 2 1)
```

Each of these is an **ambient effect** in the core: `:host/call`,
`:host/var`, `:host/static` or `:host/static-field`, answered by a reference
handler that does the real call (`doc/semantics.md` §7). Because the host is
an effect rather than a special form, a dynamic handler can intercept it,
for example to mock the file system in a test:

```klara-repl
k=> (handle :dynamic {:host/call (fn [sym & args] ((last args) [:mocked sym]))}
      (slurp "/etc/hostname"))
[:mocked clojure.core/slurp]
```

In the other direction, a Klara closure implements `clojure.lang.IFn`, so
Clojure's higher-order functions call it directly (in a nested machine;
see "The host boundary" in chapter 3):

```klara-repl
k=> (type (fn [x] x))
klara.eval.Closure
k=> (into {} (map (fn [[k v]] [k (* 2 v)])) {:a 1 :b 2})
{:a 2, :b 4}
```

Host exceptions become `:exn/raise` at the call site and are caught with
`try`, as in Clojure (chapter 3).

## Linked and hosted code

Clojure code can take part in two ways (`doc/background/01-core-v2.md` §9):

| Level | How | What you get |
|---|---|---|
| **L0 linked** | plain `require`; the code is compiled by Clojure | everything runs; its state lives outside the world and is **shared by all forks** |
| **L1 hosted** | the code is expanded by Klara's expander | its definitions live in the world: recorded reads, redefinition with invalidation, forks |
| **L2 Klara-idiomatic** | uses Klara's own names (`handle`, `perform`, `fork`, …) | the full language |

Everything you type at the Klara REPL is hosted. Every clojure.core
function you call is linked. Linked state is the visible difference: an
atom is a host object, so a fork does not copy it.

```klara-repl
k=> (def counter (atom 0))
#'counter
k=> (def w (perform :world/fork))
#'w
k=> (perform :world/eval-in w '(swap! counter inc))
1
k=> @counter
1
```

The fork's `swap!` changed the parent's atom. RFC 0001 plans to make hosted
atoms branchable cells and to treat Java objects as resources (authority
that is transferred, never duplicated); neither exists yet. Loading a
Clojure namespace as hosted code (`require-hosted`) is also design only;
today hosted code is what you define at the REPL or with
`klara.defs/define!`.

## The naming rule

> Same name ⇒ same behaviour on programs that do not fail. Different
> behaviour ⇒ a different name, or an error.

Klara's primitives (`+`, `assoc`, `first`, …) use clojure.core's functions
as their reference implementation. Where Klara must behave differently from
Clojure, it either picks a new name or turns the difference into an error;
it never silently changes what an existing name returns. This lets Clojure
programmers read Klara code without a second dictionary, and lets linked
and hosted code exchange values freely.

## Tier H: host quirks, quarantined

Some host behaviour is unsound or surprising. Klara tolerates it where
interop requires it, names it, pins it with tests, and keeps it out of
Klara-native types and laws. This is **Tier H** (design principle 11,
"sound by design"). Two examples run today, because S1 still uses
Clojure's collections and lazy sequences.

**Equality and hashing disagree for negative Integer and Long keys.**
Clojure maps compare `-1` and `(int -1)` as equal, but their Java hash codes
differ, which breaks the `java.util.Map` contract:

```klara-repl
k=> (= {-1 :x} {(int -1) :x})
true
k=> (= (java.util.Objects/hashCode {-1 :x}) (java.util.Objects/hashCode {(int -1) :x}))
false
```

Klara's own collections, when they replace Clojure's, must satisfy the
`java.util` contracts; the quirk stays confined to Clojure maps.

**A lazy sequence that failed once looks empty afterwards.** Realizing it a
second time returns no elements instead of raising again:

```klara-repl
k=> (let [s (map (fn [x] (if (= x 2) (throw (ex-info "bad" {})) x)) [1 2 3])]
      [(try (doall s) (catch Exception e :failed))
       (try (vec s) (catch Exception e :failed-again))])
[:failed []]
```

The design (research note F) gives Klara's own `lazy-seq` a cached failure
that is rethrown on every access. By the naming rule this is allowed: it
turns a silent wrong answer into an error. It is not implemented; `map`
here is clojure.core's.

## Not yet implemented

- Java method calls with `.` and constructors with `new`; class names in
  value position (`clojure.lang.IFn` as a value).
- `require-hosted`; hosted atoms as branchable cells; Java objects as
  resources (RFC 0001).
- Klara's own persistent collections as JVM classes implementing
  Clojure's interfaces (prototype in `experiments/kmap/`).
- Recording clojure.core macro reads: redefining a host macro does not
  invalidate Klara code that used it.

## Klara as a reader dialect: the `:klara` feature

Klara reads Clojure syntax with reader conditionals enabled and answers to
the feature `:klara`. While Klara is hosted on the JVM, the reader also
reports Clojure's platform feature `:clj`, so `:clj` branches act as the
fallback. A `.cljc` library can therefore diverge for Klara where it needs
to — Java interop, mutable fields, protocol internals — by putting a
`:klara` branch **before** its `:clj` branch (the first matching branch
wins, as with babashka's `:bb`):

```klara-repl
k=> #?(:klara :klara-branch :clj :clj-branch)
:klara-branch
k=> [#?(:clj :clj-branch :klara :klara-branch)]
[:clj-branch]
k=> [#?(:cljs :cljs-only :default :fallback)]
[:fallback]
```

This is the porting path for the replikativ libraries Klara depends on
(raster, ansatz, spindel, datahike): they run *linked* first, then *hosted*
through Klara's expander, and the parts that must differ get `:klara`
branches — until Klara's own compiler hosts them without the Clojure jar
(self-hosting). Java source in a library (for example ansatz's kernel in
`src-java/`) stays a JVM-host dependency and needs a port for other hosts.

REPL commands are keywords in the `repl` namespace (`:repl/world`,
`:repl/fork`, …), following clojure.main's `:repl/quit`; every other keyword
is an ordinary value, as the first transcript above shows.
