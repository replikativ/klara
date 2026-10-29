# Speculative pipelining: predict, specialize, check, learn

This example is a small Klara program that learns which branch is likely,
starts the predicted follow-up, and uses the true outcome to decide whether
that work can be reused. The model and policy are ordinary Klara code.

Pipelining overlaps stages of work, often across different inputs. Here a
prediction lets the next stage of the **same request** start before its input
is fully known. Validation decides whether to reuse that work. This is
speculative pipelining: a familiar parallelization technique expressed at the
level of ordinary programs, with online learning and staged specialization.

The [guest source](../../experiments/adaptive_affine/learned_calibration.klr)
and [host adapter](../../experiments/adaptive_affine/calibration_demo.clj)
are an experimental replacement for the earlier benchmark-oriented walkthrough.
The adapter supplies two example-specific start/await effects and the existing
checked scalar compiler; these effects are not standard language primitives.

## Start with the reference program

A batch containing a reading above 100 selects `:alert`; otherwise the mode is
`:normal`. That mode selects the calibration of a separate raw value `x`.
The constants below are illustrative, not a real sensor calibration model.

```clojure
(def calibrate
  (fn [mode x]
    (if (= mode :alert) (+ (* x 3) 10) (+ (* x 2) 1))))

(def reference-calibration
  (fn [readings x] (calibrate (classify-batch readings) x)))
```

For `x = 10`, normal mode gives 21 and alert mode gives 40. This is the
answer the speculative program must preserve even when it predicts wrongly.
The prototype admits Long raw values and uses finite numeric reading batches.

## Predict and update in Klara

The model counts observed modes. Ties choose normal. Learning happens after
**every** request, and the returned persistent model becomes the next state.

```clojure
(def predict-mode
  (fn [model]
    (if (>= (get model :normal 0) (get model :alert 0)) :normal :alert)))

(def learn-mode
  (fn [model observed]
    (assoc model observed (inc (get model observed 0)))))
```

## Specialize the follow-up with staging

The predicted mode chooses constants now; the raw value remains an argument.
This generator is also Klara:

```clojure
(def calibration-code
  (fn [mode]
    (let [gain (if (= mode :alert) 3 2)
          offset (if (= mode :alert) 10 1)]
      (code (fn [x] (+ (* x (esc (lift gain))) (esc (lift offset))))))))
```

The actual printed residuals are:

```clojure
;; :normal
(fn [x_1] (+ (* x_1 2) 1))
;; :alert
(fn [x_1] (+ (* x_1 3) 10))
```

There is no mode branch in either residual. The host adapter checks and
compiles each distinct source once per demo session; later requests reuse it.

## Put the loop together in Klara

```clojure
(def predict-and-calibrate
  (fn [model readings x]
    (let [predicted (predict-mode model)
          source (calibration-code predicted)
          job (perform :stage/demo-start source x)
          observed (classify-batch readings)
          outcome (perform :stage/demo-await job)
          reuse (and (= predicted observed) (= :ok (:status outcome)))
          value (if reuse (:value outcome) (calibrate observed x))]
      {:predicted predicted :observed observed
       :path (if reuse :reuse :fallback) :value value
       :model (learn-mode model observed)})))
```

Submission happens before classification. A worker may therefore overlap the
follow-up with classification. The host checks the session/basis when awaiting;
the guest checks the prediction before using the value. Wrong predictions and
failed worker computations use the reference follow-up. For example, overflow
in a losing speculative branch does not escape into a successful real branch.

The guest source also contains `calibration-session`, which threads the learned
state across requests. The host does not implement that learning loop.

## Run and inspect

Start one host REPL from the repository root:

```sh
clojure -Sdeps '{:paths ["src" "experiments"]}' -M
```

The bootstrap owns worker cleanup; there is no executor plumbing in the example:

```clojure
(require '[adaptive-affine.calibration-demo :as demo])
(demo/example)
```

Starting with an empty model, the four batches are `[20 22]`, `[120]`, `[121]`
and `[130]`, with `x = 10` throughout. The returned `:steps` contain:

| Batch | Predicted | Observed | Path | Value | Updated model |
|---|---|---|---|---:|---|
| `[20 22]` | normal | normal | reuse | 21 | `{:normal 1}` |
| `[120]` | normal | alert | fallback | 40 | `{:normal 1 :alert 1}` |
| `[121]` | normal | alert | fallback | 40 | `{:normal 1 :alert 2}` |
| `[130]` | alert | alert | reuse | 40 | `{:normal 1 :alert 3}` |

The predictor learns to choose alert, and only two distinct kernels compile.
Tests for this prototype are separate from the historical predictor tests:

```clojure
(require 'adaptive-affine.calibration-demo-test)
(clojure.test/run-tests 'adaptive-affine.calibration-demo-test)
```

## Why persistent worlds support larger pipelines

The useful unit of speculation can be a program region spanning functions,
library abstractions and compiler jobs. Klara's memory/world model supplies
several properties needed to make that practical:

- **Stable inputs:** persistent values can be shared with the worker without
  copying the entire reachable data graph. The caller's later persistent
  updates do not alter the worker's inputs. Opaque mutable host objects do not
  acquire this property automatically.
- **Stable code:** a pinned world fixes the definition basis while an operation
  runs. Application and optimizer code can evolve in another world without
  silently changing the speculative job's reference meaning.
- **Private changes:** a child world can retain intermediate code, data and
  proposals without publishing them to its parent. A losing branch can discard
  those changes; accepting a branch still needs the appropriate validation and
  publication protocol.
- **Explicit effects and authority:** admitted regions can compute and allocate
  privately while effectful interactions follow their authority contracts.
  This can make safe regions larger than individual arithmetic expressions;
  it does not turn arbitrary Java mutation or external I/O into rollbackable
  operations.

The opportunity is therefore broader than predicting one machine branch:
pipeline an application analysis and its consumer, or a compiler analysis and
the specialization it enables, while keeping their inputs and code versions
coherent. A prediction may stand for an abstract result, but that result must
contain **all** information the speculative continuation needs. Merely guessing
the branch direction is insufficient if the continuation also consumes other
unknown producer outputs.

The memory model supports this structure; analyses, guards, semantic evidence
and effect admission determine which actual regions are eligible. The current
prototype checks only the small scalar fragment below. Generalizing admission
across larger regions remains implementation and correctness work. Profitability
also depends on worker capacity, accuracy, validation, memory retention and
wasted work; stable snapshots alone do not establish a speedup.

## What this demonstrates and what remains open

### Autonomous use needs an investment policy

This teaching program starts speculation on every request. A running optimizer
must also ask whether overlap is worth the extra work. Resource awareness and
accounting can ground that decision in observed preparation, prediction,
training, validation, fallback and wasted-work costs, together with CPU and
memory budgets. Accuracy alone is insufficient: a correct prediction of a tiny
follow-up can still cost more than it saves.

The application chooses the objective: reduced latency may justify extra CPU
on an otherwise idle worker, while the same speculation can hurt throughput
on a saturated machine. Expected benefit must include opportunity cost and
amortization, and should be updated as outcomes and workloads change. A budget
limits the investment even when the estimate is wrong; it does not prove a
speedup. A useful policy can decline or spend a bounded amount on measurement.

The original benchmark records several of these cost components, and the
bounded guest planner demonstrates explicit investment decisions with supplied
estimates. The calibration prototype does not yet connect those pieces into a
learned profitability policy. That is the next policy layer, separate from
the checks that make an individual speculative result safe to reuse.

### Current prototype boundary

Prediction, online learning, residual construction, reuse/fallback decisions
and the request loop are in Klara. The host provides scheduling, world pins,
finite effect-free scalar admission, compilation, tickets and cache storage.
The worker admits only closed unary Long expressions over +/* and literals;
there are no world reads, callbacks, loops or arbitrary host effects. Its child
world and fresh authority store do not inherit the caller's continuation.
Tickets are session/basis-specific and consumed once.
This prototype awaits every submitted job, including losing jobs. Avoiding
that wait needs an explicit discard/cancellation and resource-settlement
protocol; it is not hidden behind a claim of optimal scheduling here.

This is a restricted executable experiment, not a general speculation sandbox
or a performance result. Scheduling and compilation dwarf this tiny arithmetic.
The next performance workload should keep the same structure and use a larger
checked numerical follow-up, with preparation and wasted-work costs measured.

The semantic obligation is that `run(calibration-code(mode))(x)` agrees with
`calibrate(mode, x)`, including checked-arithmetic behavior. The prototype tests
that obligation and tests reference agreement, changed predictions, stale-basis
and effect rejection, ticket reuse and losing-branch overflow. It does not add
a kernel proof of the generator or the concurrent scheduling protocol. The
existing scalar compiler's proof/trust boundaries still apply.
Compilation failure also falls back and still trains on the true observation.

The earlier [predictor benchmark](../../experiments/adaptive_affine/predictor.clj)
and its [recorded measurements](../../experiments/adaptive_affine/README.md)
remain separate evidence for host-orchestrated speculation. Its training and
scheduling measurements have not been relabeled as results for this prototype.
