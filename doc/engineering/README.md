# Engineering guide

Choose a route:

- **Use Klara:** [project status](../../STATUS.md), [language guide](../guide/README.md),
  [examples](../../examples/README.md), then [funded preparation](preparation-strategies.md).
- **Change implementation:** [architecture](../architecture.md), [codebase map](codebase-map.md),
  [compiler](compiler.md) or [runtime](runtime.md), then the relevant source/test.
- **Assess a claim:** [correctness ledger](correctness.md) or [performance](performance.md),
  followed by its attributed raw cohort. [Artifact commands](../artifact.md) are
  the release/reproduction authority.

| Contract | Maintained account |
|---|---|
| Bindings, worlds and stages | [Bindings/modules](bindings-and-modules.md), [Code views](code-views.md) |
| Preparation and checked composition | [Strategies](preparation-strategies.md), [guest local calls](guest-local-calls.md), [recipe composition](recipe-composition.md) |
| Ownership and consumer boundary | [Private accumulators](private-accumulator.md), including model theorems and tested bridges |
| Lowering and recovery | [Ordered transfers](transfers.md), [interpreters](../interpreters.md) |
| Validation and runtime entry | [Candidate selection](candidate-selection.md), [preparation costs](preparation-costs.md) |
| Explicit investment and scheduling | [Investment policy and scheduling](investment-policy.md) |
| Current costs | [JVM campaign](../../experiments/baseline/campaign-results/README.md), [entry](../../experiments/baseline/entry-results/README.md), [investment](../../experiments/baseline/investment-policy-results/README.md) |

[Maintained verification](../../verification/README.md) is separate from
[active diagnostics and dated evidence](../../experiments/README.md). Historical
results describe their exact cohorts, not the latest checkout. Generated reports
live in `target/verification/`. Public docs describe maintained contracts;
private research, development transcripts and superseded plans live in the
ignored `.internal/` directory and are not build dependencies.

Longer-term directions are described in [objectives](../objectives.md) and the
[RFCs](../../rfc/README.md). Runtime alternatives and the
[Chez study](../../experiments/interpreter/CHEZ-EMPIRICAL.md) remain attributed
experimental evidence; they add no runtime dependency.
