# Staged helper exposure followed by private accumulation

2026-10-30. A REPL composition experiment using existing passes, with no new
production rewrite or ownership rule.

```clojure
(fn [n bias]
  (let [step (fn [acc i]
               (assoc (assoc acc 0 (+ (nth acc 0) i))
                      1 (+ (nth acc 1) bias)))]
    (loop [i 0 acc [0 0]]
      (if (< i n) (recur (inc i) (step acc i)) acc))))
```

The existing ownership analyzer rejects the original helper because its closed
helper-summary interface cannot express the captured `bias`. The guest use
analysis and checked local inline expose that scalar capture as ordinary outer
data. Re-analysis then accepts the same functional accumulator conversion:
private storage for two Long slots, snapshot reads, ordered updates and final
freeze. Native preparation uses the existing inferred-affine backend.

The result at `[10000 1]` is `[49995000 10000]`. Tests compare result/container
and element classes, values and failure observations on six input pairs,
including checked overflow. A retained `[3 3]` result stays unchanged after a
later call. The installed residual records native hits with no fallback in
these admitted cases. It has its own Core entry identity; this experiment does
not yet install the whole composed rewrite under the original source identity.

## Observation boundary matters

This uses the existing private fragment's restricted observation contract, not
full equivalence under every host observer. A concrete counterexample is kept:
two zero-iteration calls to the original return the same literal vector object;
the owned implementation freezes equal but distinct vector objects. `identical?`
can distinguish them even though their values and element classes agree.

That is consistent with the documented exclusion of arbitrary host identity
from the private model. It prevents treating this prototype as a generally
backward-compatible Clojure optimization. Before broader automatic use, the
compiler needs an explicit observation contract, a representation boundary
that disallows those observations, or a lowering that preserves the required
identity/metadata/class behavior. Merely establishing affine access is not
enough. See the [current correctness boundary](../../doc/engineering/correctness.md).

## Family to develop next

The useful family is ordinary persistent accumulator loops, rather than a
particular numeric formula. Admit increasingly broad helper, branch and index
patterns through shared facts. Representation selection can choose scalar
fields, a private typed buffer or a mutable builder, depending on the admitted
shape and observations. Input buffers may require a private copy; proving that
updates can reuse that copy is different from proving exclusive ownership of
the caller's original storage.

Histories retaining old states must remain meaningful. Unknown callbacks,
effects, fork-visible aliases and representation-sensitive observers need
rejection or explicit boundaries. For map/builders, hashing and equality of
arbitrary host objects also need an effect contract. Returned materialized
outputs still require storage; affine conversion does not eliminate a
program's required output size.

Measure allocation as a function of iteration count, end-to-end time and
preparation cost against the same generic compiled source and host Clojure.
This probe records no allocation reduction or throughput measurement, and
establishes no comparison with Rust/Zig. The simulation and source-to-owned
correspondence remain proof tasks, alongside the model/host bridges.

## Reproduction

```clojure
(require '[baseline.affine-composition :as composition])
(composition/run-study! "repl-new")
(require 'baseline.affine-composition-test)
(clojure.test/run-tests 'baseline.affine-composition-test)
;; 2 tests, 8 assertions
```

The [report](affine-composition-results/repl-0.edn) retains the accepted ownership
facts, inline receipt, differential observations, identity counterexample and
source fingerprints. New reports go under `target/affine-composition/`.
Only the inline stage is charged to this experiment's bounded job counter;
ownership inference and native preparation have their existing separate path.
This is not yet one fully metered composed preparation job.
