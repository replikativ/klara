# Ordered transfers: examples and proof boundary

A transfer computes the values for a new set of bindings. It is not a transfer
of authority or ownership permission. The shared plan evaluates RHSs in source
order against old bindings, then commits the results.

These examples run through the existing staged scalar compiler and installed
execution path, with checked Long arithmetic. The diagnostic harness observes
the actual plans passed to the Java emitter, instantiates the universal theorem
for them, and compares compiled results with T0.

The opt-in [generic baseline](compiler.md#consolidated-implementation-boundaries) also consumes
ordered plans at local self-tail backedges. Its bounded Klara producer constructs
the records; `check-transfer!` independently binds their argument CodeIDs and
destinations before Clojure emission creates temporary lets and `recur`.
`:transfer-receipts` identifies the actual producer. This new adapter remains
tested: the universal theorem has not become a proof of Clojure/JVM emission.

## Swap and permutation

```clojure
(fn [n]
  (loop [i 0 a 1 b 2]
    (if (< i n)
      (recur (inc i) b a)
      (+ (* 10 a) b))))
;; n=0,1,2,7 => 12,21,12,21
```

The backedge computes `[old-i+1, old-b, old-a]`. Sequential assignment `a=b;
b=a` would lose old `a`. Fresh temporaries retain all next values before any
parameter write. The same mechanism supports rotations of more values.

## Several dependent variables

```clojure
(fn [n]
  (loop [i 0 a 1 b 2]
    (if (< i n)
      (recur (inc i) b (+ a b))
      a)))
;; n=0,1,5,12 => 1,2,13,377
```

New `b` uses old `a` and old `b`. No recurrence-specific compiler rule or
closed-form identity is involved. Checked overflow remains an error, even if
the eventual return would omit the overflowing parameter.

## Condition-driven loops with multiple backedges

```clojure
(fn [x y]
  (loop [a x b y]
    (if (> a b)
      (recur (- a b) b)
      (if (< a b)
        (recur a (- b a))
        a))))
;; positive inputs (48,18), (21,14), (17,17) => 6,7,17
```

This subtractive Euclidean algorithm has no known trip count or fixed stride.
The structural view finds two backedges, each with its own transfer plan.
Only the selected branch executes. The existing compiler handles this shape;
the transfer theorem does not establish algorithm termination. Zero/negative
inputs require their own behavioral specification.

## Calls and private updates need additional contracts

```clojure
(f (inc a) (+ a b))
```

First resolve/evaluate `f` in the correct order, then evaluate arguments and
place them in a new activation. The same argument protocol is useful, but
callee entry, tail calls, continuations, world basis and capturing effects need
separate ABI/proof rules. This theorem does not license arbitrary native calls.

```clojure
(assoc v 0 (nth v 1) 1 (nth v 0))
```

Both RHSs read old `v`. A private mutable implementation can use temporaries
and stores only after ownership/retention evidence licenses that representation.
Repeated destinations have last-write semantics and need a separate adapter;
loop parameters have distinct destinations. Call and owned-update integration
remain subsequent work.

## The checked statement and its limits

[`consolidation.transfer`](../../verification/consolidation/transfer.clj) defines
an ordered evaluator with explicit success/error results. Its target retains
values in pure continuations until commit. Six checked statements cover helper
congruence, universal transfer equality, pointwise evaluator equivalence,
success and failure. They quantify over any finite RHS list, Type-0 value,
error and expression types, and total pure evaluators. Failure retains the old
parameter list and the same modeled error. Commit is an arbitrary pure function.

This target is a model of deferred commit, not bytecode semantics. The hosted
`loop/check-transfer!` independently checks source order, temporary indices
and the complete commit mapping. Kernel ordinals denote actual RHS positions;
receipts bind representation-sensitive CodeIDs and plan identity, plus kernel,
import cohort and model dependency fingerprint. Programs of the same arity can
reuse the same theorem instance: it proves the transfer protocol, not a
numerical equality between those programs.

The adapter, variable lookup, expression-to-Java lowering, physical locals and
host compiler remain tested implementation bridges. Pure continuations abstract
fresh temporaries; no full imperative slot-machine simulation is claimed.
Separate expression equivalence evidence can discharge the pointwise evaluator
premise. Imported Init remains loaded in TRUST mode; new terms are checked in
the captured environment.

No parameter commit occurs in the modeled failure path. Earlier real external
effects would nevertheless remain. Pure scalar execution is the first admitted
interpretation. Authority, observable host mutation, divergence, interruption
and exact resource metering are outside the theorem's observations.

## Integration and reproduction

Scalar Java emission checks the plan it actually consumes against the original
arguments/destinations. Ordinary compilation does not load the proof model.
Diagnostic certification instantiates a prechecked theorem without per-program
tactics. Whole candidates remain `:tested`; this component result is not a
whole-compiler proof or an installation permission.

```sh
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m consolidation.transfer-examples
clojure -M:verify
```

The first command instruments one hosted compilation at a time using
`with-redefs`. It is a diagnostic harness, not a concurrency-safe compiler
service. The verification report exports six named theorem receipts. Tests
reject reordered/missing RHSs, duplicate temporaries, changed commits, stale
receipts and Long-to-BigInt literal changes. No preparation speedup is claimed.

## Shared structural boundary and recovery

Keep Core as reference meaning and K1 as existing named lowering. `loop/view`
recognizes an admitted direct self-tail region; the transfer descriptor specifies
ordered evaluation into temporaries followed by simultaneous commits. Scalar,
generic Clojure and owned consumers share that structural contract while
retaining their distinct arithmetic, initialization and storage rules. Pattern
or another dialect validator may check grammar at pass boundaries; grammar
checking cannot establish effects, ownership or semantic simulation.

Recovery uses `eval/materialize` and `stage/frame-states-error`, not a second
snapshot format. A descriptor needs the original CodeId/resume position,
ordered pending continuation, full logical environment, capture prefix,
recursive aliases, code basis and closure mint basis. Live authority comes from
the actual execution, never serialized/cloned constants. Certificate digests
bind structure; they do not establish that a fabricated state is reachable.

At a completed loop transfer, RHS evaluation and commit have both completed.
Failing RHS work is still spent work even without a committed semantic snapshot.
Completed iterations, T0 transitions and emitted instructions are different
accounting units. Exact-step requests stay in T0 absent exact correspondence.
A bounded iteration count does not bound elapsed time inside a call.

Capturing calls/effects require explicit guest control and a represented pending
continuation after ordered argument evaluation; direct host calls require a
transitive no-capture contract. Recovery must preserve prior effects. Lazy
creation/forcing contexts, async cancellation, fork/borrow settlement and staged
frames remain barriers until represented. No arbitrary native-stack capture or
interior private-array materialization is claimed. See [sourir's explicit
assumptions/state translations](https://www.o1o.ch/about/sourir/) for related
reasoning, not a proof of Klara's world/authority model.
