# Engineering evidence

These are maintained accounts of the implementation and its limits. Start with
[project status](../../STATUS.md), the [language guide](../guide/README.md) and
[checked specialization](../checked-specialization.md).

| Document | Purpose |
|---|---|
| [Runtime contracts](runtime.md) | Worlds, authority, syntax, staging and recovery boundaries |
| [Correctness](correctness.md) | Model statements, implementation bridges, counterexamples and open obligations |
| [Performance](performance.md) | Measurement provenance, costs, losing cases and reproduction entry points |
| [Interpreters](../interpreters.md) | Formal step semantics, T0 CEK and differential tests |

Proof sources, regression cases and raw measurements remain tracked alongside
the implementation. Historical results describe their recorded source and
runtime cohorts; they are not new measurements of the current checkout.
Current verification reports are generated under `target/verification`.

Private manuscript work, raw review prompts and development discussions belong
in the gitignored `.internal/` directory. Public documentation and source
packages must stand on their own without reading that directory.
