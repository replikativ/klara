# Ownership: affine regions as checked staged rewrites

Status: design. Nothing in this document is implemented in the nucleus yet;
the earlier prototype (tag `prototype-2026-10-31`) implemented a hosted
version, described at the end.

## The idea in one paragraph

An affine region is not a different meaning for a program. It is a
representation choice: inside a region, a value that is used linearly may be
updated in place, because nobody can observe the difference. So "making code
affine" is an optimization, and it goes through the same pipeline as every
other optimization ([02-compilation.md](02-compilation.md)): a Klara recipe
proposes owned code, and the kernel admits it only if it means the same as
the reference. What is new is how the kernel checks it, and that check splits
into one theorem proved once and one test run per candidate.

## The owned fragment is Clojure's transient discipline

Klara does not need new surface forms. Clojure already has a vocabulary for
in-place updates of persistent data, with a usage rule every Clojure
programmer and model knows: transients.

```clojure
;; reference                                  ;; owned candidate
(loop [i 0 acc []]                            (persistent!
  (if (< i n)                                   (loop [i 0 acc (transient [])]
    (recur (inc i) (conj acc i))                  (if (< i n)
    acc))                                           (recur (inc i) (conj! acc i))
                                                    acc)))
```

Clojure checks the transient rule only partly, at run time. Klara checks it
statically, as the *ownership judgment* `WO`, on the candidate:

- an owned token comes from `transient` and ends at `persistent!`;
- each token is used at most once on every control path (affine), and the
  result of `conj!`, `assoc!`, `dissoc!`, `disj!`, `pop!` is the next token;
- a token never escapes: it is not captured by a closure, stored in data,
  passed to an unknown function, compared, hashed or returned from the region
  except through `persistent!`;
- reads (`get`, `nth`, `count`, `contains?`) consume nothing, but must not
  follow the token's consumption.

**Erasure** maps owned code back to functional code: `transient` and
`persistent!` become the identity, `conj!` becomes `conj`, and so on. Erasure
defines the meaning of owned code.

## How a candidate is admitted

```text
reference R ── recipe (Klara) ──> owned candidate C
                                   │
             1. WO(C)              │  the ownership judgment, a decision procedure
             2. erase(C) ≡ R       │  the existing definitional checker (L4.check.*)
             3. lower(C)           │  owned ops become Clojure transient ops
```

The theorem that makes this sound is proved once, about the formal semantics:

> **Erasure.** For every closed `C` with `WO(C)`, running `C` with a store of
> mutable cells reaches the same observations as running `erase(C)`.

Then step 2 is automatic for every candidate: no recipe author writes a
proof. Step 1 is a decision procedure; following `wsb-WS` (the closedness
check of `run`), it is defined in ansatz, compiled, and proved sound, so the
ownership checker itself is verified. Step 3 (lowering to JVM transients)
stays trusted and is tested differentially, like the rest of the backend.

The formal semantics gains a store: `Config` gets a heap of cells, `Tm` gets
`own`, `freeze` and the cell operations, and erasure is a function on `Tm`.
The erasure proof is a simulation: an invariant relates each live cell in the
store to the substituted value the erased term holds at the same point.
Linearity is what makes the invariant hold: no second reference to a cell
exists that could observe the update.

## Klara programs do the rewriting

Recipes are Klara code over Code views ([02-compilation.md](02-compilation.md)),
not hosted transformations behind a policy switch. Two library layers:

**Loop recognition** (`klara.compiler.loops`). A loop in Core is a
self-recursive function applied once, with `recur` in tail positions. The
library finds them and describes each as data:

```clojure
{:bindings [{:name i :init <code> :update <code at each recur>}
            {:name acc :init <code> :update <code> :uses [...]}]
 :exits [<code> ...]}
```

**Accumulator ownership** (`klara.compiler.recipes.owned`). For each loop
binding whose updates are persistent operations on the previous value
(`conj`, `assoc`, `update`, `disj`, `dissoc`), that is not otherwise used
after the update, and that leaves the loop only through its exits, the recipe
rebuilds the loop with `transient` at the init, the `!` operations at the
updates, and `persistent!` at the exits. It uses `code`, `esc` and the view
constructors, so it is a staged program that writes the candidate.

```clojure
(defn own-accumulators [reference]
  (code/rewrite reference
    (fn [c]
      (when-let [l (loops/loop-view c)]
        (let [owned (filter owned/linear-accumulator? (:bindings l))]
          (when (seq owned) (owned/rebuild l owned)))))))

(compiler/optimize! 'app/frequencies* {:recipe own-accumulators})
```

The recipe can be wrong. If it marks a binding that escapes or is used twice,
`WO` rejects the candidate. If it changes anything else, the definitional
check of the erasure rejects it. Either way the reference keeps running.

The same loop library is the place for the other loop rewrites the prototype
explored: fusing `map`/`filter`/`reduce` chains into one loop
(definitional, checked by unfolding), and counted loops on primitive longs
(which need a premise: an argument guard, or a certificate, L4.check.certificate).

## How it ties into the memory model

- **Lifetimes** ([01-lifetimes.md](01-lifetimes.md)). An owned token is an
  affine resource whose lifetime is the dynamic extent of its region. It is a
  root only while the region runs; `persistent!` is the only way out, and it
  costs O(1). The collectability obligation: after a region exits, nothing
  but the frozen value is reachable from its tokens.
- **Bounded memory.** The point of the rewrite: a loop that builds a vector
  allocates a new path-copied root per iteration in the reference, and
  updates one transient in the candidate. Allocation, not just time, is part
  of what the benchmark reports.
- **Continuations and forks.** A continuation captured inside a region would
  let the program resume twice and observe the mutation. Compiled regions
  cannot perform effects (L4.lower.subset), so nothing is captured inside
  them. If owned code is ever interpreted, a region frame makes every
  continuation that holds it one-shot, and a second resume raises
  `L3.affine.reuse`, the rule the spec already reserves.
- **Jobs.** A transient created inside a job belongs to the job, like atoms
  created in it (L3.job.host-mutation). A fork never copies a token: forking
  a continuation that holds a region frame is refused.

## What the interpreter does and does not do

The interpreter optimizations of the performance milestone are host code in
the trusted runtime (`klara.runtime.machine`, `klara.runtime.prepare`). They
change representation, not meaning, and are guarded by the differential
tests against the formal semantics. Ownership is different: it is a source
rewrite with an observable boundary, so it belongs to the compiler pipeline,
where guest programs propose and the kernel checks. The interpreter runs the
reference; owned code runs compiled.

## Plan

1. **Views for loops.** Extend `klara.code` views with `:recur`, function
   self names and multiple arities; add `code/rewrite`.
2. **Owned Core in the checker.** `WO` as a host decision procedure first;
   erasure; admission as above; lowering to transients.
3. **The loop library and the accumulator recipe** in `lib/`, with the
   benchmark's `maps` and a vector-building loop as acceptance programs,
   plus rejection cases (escaping token, double use, unknown call).
4. **Formal.** Store semantics in `spec/formal`, `WO` defined in ansatz with
   a soundness proof, and the erasure theorem. Then replace the host `WO` by
   the compiled verified one.
5. **Primitive arrays.** `long[]` for numeric accumulators under argument
   guards or certificates, the prototype's private-accumulator family.

## What the prototype did, and what changes

The prototype had surface ownership forms (`own`, `update!`, `borrow`,
`freeze`) checked at run time by the authority store, a static affine checker
producing derivations, and an inferred-accumulator conversion to private
`long[]` loops. The analysis and the rewrite were hosted Clojure; guest code
only chose among fixed hosted actions (`:local-call`, `:private-accumulator`).
Its proofs were about a separate finite model (`PrivatePlan`), connected to
the real terms by tested bridges.

The design above changes three things: the rewrite is a Klara program; the
owned fragment is the transient discipline, so erasure is simple and the
reference is ordinary Clojure; and correctness splits into one theorem about
the real semantics plus an automatic check per candidate.
