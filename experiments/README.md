# Experiments and evidence

Start with the current result, then follow its reproduction sources. Maintained proof/model/scenario dependencies now live in
[`verification/`](../verification/README.md); active benchmark drivers stay here. Historical
measurements retain their original source, JVM and observation scope; they are
not measurements of the latest checkout.

| Entry | Role | Start here |
|---|---|---|
| Stage/world binding diagnostic | Late versus consumed world dependencies and the conservative pinned-closure rejection | [Binding account](../doc/engineering/bindings-and-modules.md#current-staging-support-and-an-open-world-binding-contract), `consolidation/stage_world_bindings.clj` |
| Actual syntax and bounded investment | Indexed lexical model/implementation checks, four-policy finite traces and refreshed five-family JVM cohorts | [Correctness slice](../doc/engineering/actual-inline-correspondence.md), [study](baseline/investment-policy-results/README.md) |
| Entry resolution and dispatch | Live host checks, matched traversal controls, direct priority recovery and allocation | [Implemented slice](../doc/engineering/candidate-selection.md#live-entry-plans), [study](baseline/entry-results/README.md) |
| Preparation attribution | First backend loading, single/repeated production controls and uninstrumented paired costs | [Implemented slice](../doc/engineering/preparation-costs.md), [study](baseline/preparation-results/README.md) |
| Current JVM compiler campaign | Three fresh-process cohorts; phase costs, allocation, declines and candidate portfolios | [Campaign report](baseline/campaign-results/README.md), `scripts/run_compiler_campaign.py` |
| Current composed optimization | Inline a helper, admit private state under an enclosed consumer, retain original entry identity | [Implementation](../doc/engineering/private-accumulator.md), [diagnostics](baseline/private-accumulator-results/README.md) |
| Fork measurement admission | Pure source/input replay, rejected host effects, fuel limits; no automatic promotion | [Preparation account](../doc/engineering/preparation-strategies.md#measuring-a-candidate-in-a-fork), `verification/baseline/fork_benchmark.clj` |
| Proof and composition verification | Models, implementation bridge tests, negative cases and receipt exports; actively imported by `:verify` | `verification/consolidation/run.clj`, [correctness ledger](../doc/engineering/correctness.md), `clojure -M:verify` |
| Earlier baseline studies | Wider coverage, cold preparation, loop emission, ownership and staged policies | [Baseline index](baseline/README.md), linked per-cohort reports and frozen sources |
| Interpreter and runtime alternatives | T0 representation, recovery, JVM interpreter controls and Chez studies; retained evidence for the fallback cliff | [Interpreter index](interpreter/README.md), [public interpreter guide](../doc/interpreters.md) |
| Other specialization families | Numerical proofs, predictor, fusion, typed emission, handlers and owned-region investigations | `../verification/proof_staging/`, `../verification/adaptive_affine/`, `history/typed_jit/`, `history/staged_regions/`, `handlers/`, `affine/`; follow each report's scope |

The campaign's [initial failure and corrected instrumentation cohorts](baseline/campaign-results/README.md#measurement-scope-and-corrections)
explain fixes and remain separate from the current aggregate. Old source
snapshots, negative cases and unique raw samples are evidence, not disposable
build outputs. Current generated verification belongs under `target/verification`.

Historical compiler, S7 entry, typed-JIT and staged-region bundles live in
`history/`, retaining original namespace layouts through `-M:history`.
Frozen source manifests retain original paths/hashes. Sixteen identical initial
investment snapshots refer to retained frozen copies; the two differing initial
sources remain separate. Unique samples, failures and negative cases remain.
Private manuscript strategy and development discussion stay in `.internal/`.

The [artifact guide](../doc/artifact.md) explains packaging and fresh-process
checks. The [agent-assisted evolution objective](../doc/objectives.md#agent-assisted-program-evolution)
describes the intended agent integration; it does not imply that these retained
benchmarks already form an autonomous improvement system.
