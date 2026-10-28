# Demo plan: wandler with staging, applied systematically (draft for discussion)

**Goal.** Show the Klara architecture working on a non-trivial JIT before
porting the stack: a data-pipeline runtime that specializes itself from
measurements, certifies every adopted rewrite in ansatz, swaps safely while
running, survives REPL edits of its own stages, and tries alternative plans in
forks — with receipts. Built from a Clojure REPL on existing code (wandler,
ansatz, spindel, v0's world and X1), with Klara as a library. No Klara syntax
needed yet.

## What wandler has today (`../wandler/docs/JIT.md`)

- Elaborate → certified rewrite in ansatz → lower to Clojure (translation
  validation per program).
- Planning JIT (`optimize-measured`): measure statistics, re-plan.
- Hot-swap JIT (`jit/swap`, `PSwapNode`, `run-adaptive`), spindel and DBSP
  swap variants (`swap_spindel.clj`, `swap_dbsp.clj`), strict PGO replay
  (`jit/pgo.clj`).
- Stated gaps: swap cells accept ordinary functions and do not check
  certificates; state migration certificates, drift triggers and compilation
  budgets are future work; `jit-stream` re-plans once after warmup.

## What "staging applied systematically" adds

Every gap above is an instance of a Klara mechanism:

| Wandler gap | Klara mechanism | Doc |
|---|---|---|
| swaps of uncertified functions | an executable may be installed only with a certificate matching (CodeId, guards); the swap cell checks it | v2 §3, §7 |
| re-plan once | specialization as a tracked node keyed by (pipeline CodeId, assumptions); drift = guard failure → generic path → asynchronous re-plan | v2 §6, C §4 |
| no budgets | per-node optimization budget split from the session budget; churning sites go generic (R5) | v2 §2, §10 |
| state migration | swaps only at window boundaries (entry) or with a declared state-transfer contract | v2 §6 |
| editing a stage while running | the stage is a world definition (X1); the stream fiber raises its basis at a window boundary; old windows finish on the old basis | v2 §6, X1 |
| choosing between plans | fork two plans with coupled inputs; join by measured value; selection evidence separated from the reported claim | v2 §2, E §4.3 |
| proof cost | ansatz proves small closed facts within a background budget (50 ms per candidate); timeout → generic | Codex challenge §4 |

## Scenario

A streaming pipeline over the city data (purchases joined with residents,
grouped by district, with a filter and a map), with a data distribution that
drifts (a shopping centre closes mid-stream).

1. Start generic. Wandler certifies fusion and the group-by-over-join
   factorization (O(N²) → O(N)); the specialized plan is installed with its
   certificate.
2. The distribution drifts; a cardinality guard fails; the stream continues
   on the generic plan; a new plan is proved and installed in the background
   within budget.
3. At the REPL, edit the filter stage. The edit publishes immediately (R1);
   the stream adopts it at the next window boundary; windows in flight finish
   on the old basis.
4. Fork two optimization strategies on coupled input windows; adopt the
   better one on held-out windows; the receipt shows proof ids, guards,
   selection evidence and claim evidence separately.
5. Delete every cache: results and traces are unchanged (R3).

## Experiments, in order

| # | What | Decides |
|---|---|---|
| W0 | Reproduce (or refute) the ansatz `check-constant-replace` issue and the v0 dispatch firewall issue through public APIs | whether certificates can be trusted; fix first if confirmed |
| W1 | Certificate-checked install: the swap cell accepts an executable only with a certificate for (CodeId, guards) | closes wandler's main trust gap |
| W2 | Specialization as a tracked node with an assumption set (X1 graph now, spindel later per X6) | the staging mechanism on a real optimizer |
| W3 | Drift: guard failure → generic → asynchronous re-plan with a budget; measure time-to-recover and foreground cost | "never on the critical path" in practice |
| W4 | REPL edit of a stage under a running stream; basis raise at window boundaries; gates R1, R2, R4 | the REPL story |
| W5 | Forked plan comparison with coupled windows; receipts with selection vs claim evidence | forks and receipts on a real workload |
| W6 | Ansatz staging of small facts (fixed dispatch, no suspension) with a 50 ms budget; measure proof cost vs saved cost | whether proof staging pays |
| W7 | Raster as the optimizing tier for numeric stages | the narrowing ladder end to end |

W0–W4 are the core demo; W5–W7 extend it. Each lands as code plus an update to
the relevant RFC.

## Open questions for Christian

1. Is a streaming city pipeline the right scenario, or should the demo stay
   on wandler's existing benchmarks first (less setup, less impressive)?
2. Should W1 change wandler itself (swap cells check certificates) or wrap it
   from the Klara side first?
3. ansatz or raster next after the demo: a reimplementation in Klara, or
   integration through Klara's interfaces? (My lean: integration first;
   reimplementation only where Klara's staging gives something concrete.)
