# Inferred private mutation and outcome speculation

This experiment turns an ordinary functional accumulator into a private mutable
buffer, automatically, in a deliberately restricted fragment. It connects the
conversion to the existing ownership checker, eraser, actual Klara authority
fork, prepared candidate and guarded stage cache. A companion host experiment
learns a binary outcome predictor and executes the checked follow-up in a
persistent world fork. Both retain the original computation as the reference.

For a smaller experimental version with prediction, learning and staging in
Klara, see [example16](../../examples/staging/16-learned-speculation.md).
Its prototype tests run separately. The original host predictor's three tests
remain in `clojure -M:verify`; historical timing reports remain separate.

Start one Clojure REPL at the repository root and keep it running:

```sh
clojure -Sdeps '{:paths ["src" "test"]}' -M
```

```clojure
(require '[clojure.test :as test]
         '[klara.infer-affine-test]
         '[klara.affine-test]
         '[klara.staged-compile-test])
(load-file "experiments/adaptive_affine/bench.clj")
(load-file "experiments/adaptive_affine/predictor.clj")
(load-file "experiments/adaptive_affine/predictor_test.clj")
(test/run-tests 'klara.infer-affine-test 'klara.affine-test
                'klara.staged-compile-test 'adaptive-affine.predictor-test)

;; Optional diagnostics; overwrite the corresponding recorded artifacts.
(adaptive-affine.bench/run!)
(clojure.java.io/make-parents "target/predictor/results.edn")
(adaptive-affine.predictor/run! "target/predictor/results.edn")
```

The JDK is needed by the existing S23 compatibility tests. No dependency override,
new dependency, subprocess-per-compilation or sibling repository edit is needed;
the pinned ansatz version remains 0.2.115. `bench.clj` uses the JVM thread
allocation/CPU MXBean and `.threadId`, as available in the recorded JDK 25.

To see the policy execute in Klara:

```clojure
(require '[klara.authority :as a] '[klara.defs :as d]
         '[klara.stage :as stage] '[klara.world :as w])
(def world (adaptive-affine.bench/load-world))
(def cache (stage/make-cache))
(binding [a/*store* (a/new-store)]
  (stage/with-cache cache
    (d/eval-form (w/snapshot world)
      '(operate-counter (counter-controller counter-code 1)
                        [[3 1] [5 2] [8 3] [2.5 1]] 2))))
;; :values [[1 2] [2 3] [3 5] [1 2]]
;; :controller has :attempted true, :budget 0 and :publication :installed.
```

Pass the returned `:controller` to the next batch. The threshold counts Long
argument observations; it does not establish aliasing facts or predict benefit.
The controller is explicitly single-owner persistent state: reusing an older
state can intentionally repeat an attempt. This is not a concurrent once-only
coordinator. The example expects a positive threshold and nonnegative budget.

Artifacts:

- [`08-inferred-affine.klr`](../../examples/staging/08-inferred-affine.klr):
  actual `code`/`esc`/`lift` generation and persistent adaptive controller.
- [`infer_affine.clj`](../../src/klara/compile/infer_affine.clj): automatic
  conversion, inspectable evidence and preparation adapter.
- [`results.edn`](results.edn): all allocation/timing samples and amortization.
- [`residual.clj.txt`](residual.clj.txt): the actual emitted Clojure function.
- [`predictor-results.edn`](predictor-results.edn): learned model, true outcomes,
  hits, misses, training, speculation and fallback costs, including repeated
  large-case samples.
- [`S25.md`](../../doc/engineering/correctness.md): design, research comparison,
  trust limits, exact evidence and next proof obligations.

Independent review found and fixed a reflective setter in the original array
emitter. Original `results.edn`, residual and predictor measurements are preserved;
they describe the old implementation. Load `review.clj` and call
`(adaptive-affine.review/run!)` for separate updated measurements, raw samples in
`review-results.edn`, and the updated residual in `review-residual.clj.txt`.
The [review report](../../doc/engineering/performance.md) explains the change
and remaining entry overhead. The speculation experiment is synthetic and its close-to-zero large-case
timings vary; a high accuracy percentage alone does not justify speculation.
