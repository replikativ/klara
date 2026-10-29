# Example 7: early model compilation and operational scalar refinement

The executable source is [07-staged-regions.klr](07-staged-regions.klr).
It generates a polynomial least-squares kernel with `code`/`esc`, stores it as a
world code value, and later uses bounded observations to request a checked JVM
specialization. The same `refine` function can be called before operation.

Load the opt-in seed backend and definitions from an ordinary Clojure REPL:

```clojure
(require '[klara.compile.staged]
         '[klara.world :as w] '[klara.defs :as d]
         '[klara.stage :as stage] '[klara.authority :as a]
         '[clojure.java.io :as io])
(def world (w/make-world))
(with-open [r (java.io.PushbackReader.
                (io/reader "examples/staging/07-staged-regions.klr"))]
  (doseq [form (take-while #(not= ::end %)
                          (repeatedly #(read {:eof ::end} r)))]
    (d/define! world form)))
(def cache (stage/make-cache))
(binding [a/*store* (a/new-store)]
  (stage/with-cache cache
    (d/eval-form (w/snapshot world)
      '(operate kernel-code [10 12 14 16 10.5] 2))))
;; {:values [7993 23838 58163 123688 14234], :long-count 2,
;;  :attempted true, :publication {:status :installed, :code-id ...}}
```

The first two calls use T0. The policy then prepares code in an authority fork
and publishes it after fork exit. The next two calls pass real Long guards.
The final Double argument falls back to T0. `stage/clear!` can remove the
executable without changing the program's values or errors.

For early compilation, evaluate `(refine kernel-code)` under the same bindings
before calling `kernel`. For a changed calibration, publish
`(d/define! world '(def calibration 7))`. Old pinned roots keep their old
meaning; the new root falls back until a new specialization is prepared.

Polynomial/model traversal and code generation execute in Klara. Scalar type
analysis and Java emission are a tested host seed backend. The example uses a
synchronous policy; independent compiler scheduling is demonstrated by a host
concurrency test, not by a new Klara scheduler. Counts and one compile attempt
are bounded per batch, not globally across repeated `operate` calls.

The precise admission, isolation and publication contract, limitations and
extension points are in [runtime contracts](../../doc/engineering/runtime.md). Run the targeted
tests with `clojure -M:test -n klara.staged-compile-test`. For diagnostic timing,
load `experiments/staged_regions/bench.clj` into a persistent REPL and call
`(staged-regions.bench/run!)`.
