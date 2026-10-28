# 10. Certified fusion

**Demonstrates:** a map/filter/reduce pipeline written in Klara, fused into
one loop by a rewrite whose correctness is a theorem checked by the ansatz
kernel; the shape claim that gates it; the guards that keep it honest when
a stage is edited; re-optimization.

**Exercises:** the guarded-specialization square and the certified-rewrite
square (`doc/semantics.md` §8); gate R3 (deleting the cache changes no
result); the checked-claim contract (`doc/background/01-core-v2.md` §7);
the S3 certificate checks (`doc/background/impl/S3.md` §2).

**Runs on:** T0 plus S3 (`klara.fusion`). S3 is driven through its Clojure
front door: a *session* is a separate world plus a specialization cache.
The transcript calls the front door from the Klara REPL as host functions
(`klara.fusion/define!` and friends), so the pipeline lives in the
session's world, not in the REPL's own world. A Klara-level surface for
claims and optimization does not exist yet. The first `optimize!` builds
the proof environment, which takes a second or two.

## A pipeline and its claim

```klara-repl
k=> (def S (klara.fusion/session))
#'S
k=> (:name (klara.fusion/define! S '(def keep? (fn [x] (even? x)))))
keep?
k=> (:name (klara.fusion/define! S '(def p (fn [xs] (reduce + 0 (map (fn [x] (* x x)) (filter keep? xs)))))))
p
k=> (klara.fusion/run S '(p [1 2 3 4 5 6]))
56
```

Nothing is optimized without a **shape claim**. The claim is a checked
claim: its argument part becomes an entry guard (the argument must be a
realized vector or list of non-negative longs, or nil), and its result part
is checked when the kernel types the elaborated term.

```klara-repl
k=> (klara.fusion/optimize! S 'p)
{:status :generic, :reason :no-shape-claim}
k=> (:name (klara.fusion/claim! S 'p '{:args [(List Nat)] :ret Nat}))
p$shape
k=> (select-keys (klara.fusion/optimize! S 'p) [:status :stages :laws])
{:status :fused, :stages [:filter :map :reduce], :laws ["Klara.foldl_map" "Klara.foldl_filter"]}
```

`optimize!` elaborated the Klara core term of `p` into an ansatz term,
rewrote it with two laws proved once in ansatz,

```
Klara.foldl_map    : foldl f b (map g l)    = foldl (λ acc x. f acc (g x)) b l
Klara.foldl_filter : foldl f b (filter p l) = foldl (λ acc x. cond (p x) (f acc x) acc) b l
```

obtained a theorem `∀ xs : List Nat, naive xs = fused xs`, lowered the
fused term to a host function, and installed it in the cache. Install
rechecks the certificate: the checker re-elaborates the recorded source,
recomputes the goal and checks the proof in the kernel.

## Running through the executable, and falling back

```klara-repl
k=> (klara.fusion/run S '(p [1 2 3 4 5 6]))
56
k=> (klara.fusion/run S '(p [1 -2 3]))
4
k=> (:hits (klara.stage/stats (:cache S)))
1
k=> (:fallbacks (klara.stage/stats (:cache S)))
1
```

The second call has a negative element. The entry guard `[:arg 0 :nat-list]`
fails, and the generic path runs instead: same answer, no theorem needed.

## Edit a stage

The executable inlined `keep?` and guards its version. Editing `keep?`
makes the guard fail, so the very next call runs the generic code with the
new predicate. Re-optimizing produces a new theorem for the same CodeId.

```klara-repl
k=> (:name (klara.fusion/define! S '(def keep? (fn [x] (odd? x)))))
keep?
k=> (klara.fusion/run S '(p [1 2 3 4 5 6]))
35
k=> (:status (klara.fusion/optimize! S 'p))
:fused
k=> (klara.fusion/run S '(p [1 2 3 4 5 6]))
35
k=> (= (klara.fusion/run S '(p [7 8 9])) (klara.fusion/run-generic S '(p [7 8 9])))
true
```

## Where fusion stops

Anything outside the elaboratable fragment makes its stage opaque and the
pipeline stays generic, with a named reason. Subtraction is not in the
fragment because `Nat` subtraction truncates while JVM longs do not:

```klara-repl
k=> (:name (klara.fusion/define! S '(def q (fn [xs] (reduce + 0 (map (fn [x] (dec x)) xs))))))
q
k=> (:name (klara.fusion/claim! S 'q '{:args [(List Nat)] :ret Nat}))
q$shape
k=> (klara.fusion/optimize! S 'q)
{:status :generic, :reason [:opaque-stage 0 :map [:prim dec]]}
```

## What to notice

- **The claim is the gate.** No claim, no elaboration. With a claim, the
  argument part is checked on every entry and the result part by the
  kernel. Inputs that do not satisfy it (negatives, doubles, lazy seqs) run
  generic.
- **Overflow.** The laws hold over `Nat`, the code runs on longs. The fused
  code uses exact arithmetic (`Math/addExact` …) and declines (deopts) on
  overflow, so the generic path runs from entry; the stages are pure, so
  the replay repeats no effect. That both paths overflow on the same inputs
  is argued, recorded in the certificate as `:trusted`, and property-tested,
  not proved.
- **Trusted parts.** The elaborator from Klara core terms to ansatz, the
  lowering table and the overflow coincidence are trusted and tested; the
  rewrite itself is proved per pipeline.
- **Deleting the cache changes nothing** (gate R3): `klara.stage/clear!`
  removes every executable, and all results stay the same (`fusion_test`).
