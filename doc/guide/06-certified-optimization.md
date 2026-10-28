# 6. Certified optimization

Klara separates what a program *means* from how it is *run*. The meaning
is fixed by the core semantics; the runtime may replace a function by
faster code, an **executable**, only under two conditions: the executable
is guarded by the assumptions it relies on, and a **certificate** says why
it agrees with the original under those assumptions. This chapter walks
through the one certified optimization that exists, S3's fusion of
map/filter/reduce pipelines with proofs from the ansatz kernel.

`examples/klara/10-certified-fusion.md` is the short version; this chapter
explains the machinery.

## The specialization cache

Every closure entry in T0 consults the cache (`klara.stage`). Executables
are keyed by the CodeId of the function and by their **assumption set**.
The cache checks these guards on entry. S3 fusion uses entry fallback and
may replay only its pure pipeline. The compile tier additionally supports
mid-body guards with explicit frame-state reconstruction (S7–S11; chapter 8),
resuming T0 at the source position without replaying prior effects:

| Guard | Holds when |
|---|---|
| `[:world s value-id]` | the basis still has this version of `s` |
| `[:arg i pred]` | argument `i` satisfies `pred` (for example `:nat-list`) |
| `[:captures locals]` | the closure captured exactly these values |
| `[:statics vals]` | a partial application fixed these values |
| `[:unhandled ops]` | no dynamic handler for any of `ops` is active in the caller's continuation |

If no executable's guards hold, the generic code runs. Deleting the whole
cache therefore changes no result, only speed (gate R3).

**Meaning.** This is the guarded-specialization square of
`doc/semantics.md` §8: `guard(x) ⇒ residual(x) = generic(x)`, and on guard
failure the generic path runs from entry. It is tested, not proved, for
S1's ten R3 programs and S3's pipelines.

## Claims are the gate

Nothing is elaborated or fused unless the programmer states a **shape
claim**. A claim is a *checked claim* in the sense of the three annotation
contracts (`doc/background/01-core-v2.md` §7): it may make execution fail
a check or take the generic path, but it never changes a successful
result.

```klara-repl
k=> (def S (klara.fusion/session))
#'S
k=> (:name (klara.fusion/define! S '(def keep? (fn [x] (even? x)))))
keep?
k=> (:name (klara.fusion/define! S '(def p (fn [xs] (reduce + 0 (map (fn [x] (* x x)) (filter keep? xs)))))))
p
k=> (klara.fusion/optimize! S 'p)
{:status :generic, :reason :no-shape-claim}
k=> (:name (klara.fusion/claim! S 'p '{:args [(List Nat)] :ret Nat}))
p$shape
k=> (:status (klara.fusion/optimize! S 'p))
:fused
```

The claim `{:args [(List Nat)] :ret Nat}` is checked twice:

- its **argument** part becomes the entry guard `[:arg 0 :nat-list]`: nil,
  or a realized vector or list of non-negative longs. Lazy sequences,
  negative numbers and doubles go generic;
- its **result** part is checked when the kernel types the elaborated term.

## From Klara term to theorem

`optimize!` takes the **core term** of `p` (not its source text, so macros
and helper definitions are already resolved) and:

1. **elaborates** it into an ansatz (Lean 4 calculus) term over `Nat` and
   `Bool`. `map`, `filter` and `reduce` appear in the core term as
   `:host/call` performs; each stage function must be an inline `fn`, a
   world definition holding one (inlined, and its version becomes a guard)
   or a primitive. Anything else makes the stage *opaque*. Elaboration is
   also the purity check: a stage that elaborates performs no effects;
2. **fuses** the pipeline by rewriting with two laws proved once in ansatz,
   `Klara.foldl_map` and `Klara.foldl_filter`, one law instance per stage,
   chained by transitivity. The result is a theorem
   `∀ xs : List Nat, naive xs = fused xs` whose right side is a single
   `List.foldl`;
3. **lowers** the fused term to a Clojure function using exact arithmetic;
4. **certifies** and **installs** it.

```klara-repl
k=> (def exe (first (klara.stage/executables (:cache S))))
#'exe
k=> (sort (map first (:guards exe)))
(:arg :captures :unhandled :world :world)
k=> (def cert (:certificate exe))
#'cert
k=> (sort (keys cert))
(:assumptions :checker :checker-version :closure :code-id :cohort :digest :laws :lowering :payload :provenance :side-conditions :source :theorem)
k=> [(:checker cert) (:checker-version cert)]
[:ansatz/kernel "ansatz/0.2.115+klara.fusion/1"]
k=> (sort (keys (:laws cert)))
("Klara.foldl_filter" "Klara.foldl_map")
k=> (mapv (juxt :condition :status) (:side-conditions cert))
[[:purity :by-construction] [:input-is-list-nat :guarded] [:reference-host-handlers :guarded] [:nat-faithful-lowering :checked-at-runtime] [:overflow-coincidence :trusted]]
```

The certificate records the source term and the stages it inlined, the laws
by hash, the theorem by name and hash, the lowering by hash, the proof
environment it was checked in (`:cohort`: the bundled Init export, by
SHA-256), and the dependency closure of the proof. The proof itself sits in
`:payload`, bound to the recorded hashes.

## Install rechecks everything

`install!` trusts nothing in the certificate. The `:ansatz/kernel` checker
re-elaborates the recorded source, recomputes the goal, checks the proof in
the kernel against that goal, recomputes the dependency closure and the
lowering, and compares them with the record. A tampered certificate is
rejected:

```klara-repl
k=> (klara.stage/install! (:cache S) (assoc-in exe [:certificate :code-id] "forged"))
!! ex-info: stage: certificate rejected: code-id-mismatch
k=> (klara.stage/install! (:cache S) (assoc exe :guards (disj (:guards exe) [:arg 0 :nat-list])))
!! ex-info: stage: certificate rejected: assumption-mismatch
```

`test/klara/fusion_test.clj` forges certificates for each of the checker's
rejection reasons, including a self-consistent certificate that carries
another pipeline's proof.

## Running, falling back, re-optimizing

```klara-repl
k=> (klara.fusion/run S '(p [1 2 3 4 5 6]))
56
k=> (klara.fusion/run S '(p (range 7)))
56
k=> (select-keys (klara.stage/stats (:cache S)) [:hits :fallbacks])
{:hits 1, :fallbacks 1}
k=> (:name (klara.fusion/define! S '(def keep? (fn [x] (odd? x)))))
keep?
k=> (klara.fusion/run S '(p [1 2 3 4 5 6]))
35
k=> (:status (klara.fusion/optimize! S 'p))
:fused
```

`(range 7)` is a lazy sequence, so the argument guard fails and the generic
code runs. Redefining `keep?` breaks the executable's `[:world keep? ..]`
guard: the next call is generic and already uses the new predicate.
Re-optimizing builds a new theorem for the same CodeId.

## Overflow: Nat proofs, long code

The laws hold over the natural numbers; the code runs on 64-bit longs. The
obligation is split:

1. the lowering maps each `Nat` operation to an exact JVM operation that
   returns the true result or throws (`Math/addExact`, `multiplyExact`, …);
   subtraction is never produced, because `-` and `dec` are opaque;
2. the executable catches `ArithmeticException` and declines (deopts); the
   generic path then runs from entry. Replaying is sound because the stages
   perform no effects. So **whenever the executable returns, its value is
   the `Nat` meaning of the fused term**, which the theorem equates with the
   naive term;
3. the generic path on non-negative longs is also exact-or-throw;
4. **trusted:** both paths overflow on the same inputs, because the rewrite
   performs the same arithmetic operations per element. This is recorded in
   the certificate as `:overflow-coincidence :trusted` and property-tested
   near `Long/MAX_VALUE`, not proved.

## What is proved, tested, trusted

| Part | Status |
|---|---|
| the two fusion laws | proved in ansatz (explicit proof terms), kernel-checked when the proof environment is built |
| fused = naive, per pipeline | proved: a theorem checked at optimize and again at install |
| elaborator (Klara core term → ansatz) | trusted; deterministic, re-run at install, differential-tested against wandler |
| lowering table | trusted; exact-or-throw by inspection and tests |
| overflow coincidence | trusted; property-tested |
| R3 (deleting the cache changes nothing) | tested on 300 inputs |

## Not yet implemented

- Shape claims as surface annotations (today: the `p$shape` world name
  written by `claim!`).
- Segmented fusion around an opaque stage; wider types (`Int`, records,
  list results); automatic background re-optimization after an edit.
- The predictor ladder that would decide *what* to optimize
  (`doc/architecture.md` §6). Today optimization is requested explicitly.
- Optimizing functions of the REPL's own world: S3 works on a session's
  world, driven through the `klara.fusion` front door.
