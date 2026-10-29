# RFC 0003: Licensed specialization — from JIT to learned components

- Status: draft; exact guarded-cache, bounded checked-specialization and guest planning subsets implemented through S32; statistical licences remain design
- Owner(s): Christian Weilbach
- Experiments: S3 (certified fusion), S4 (staging), S25 (online outcome speculation), S32 (guest planning/policy evolution); planned: distillation demo
- Obligations: LS1–LS7 below

## Motivation

Klara's staging and specialization cache were introduced for JIT-style
optimization: replace a generic computation by a faster one that agrees with
it. The same mechanism covers much more, provided the *licence* for a
replacement is explicit. Worked example (Christian, 2026-10-28):

> A frontier LLM observes a Klara agentic workflow, notices that one call site
> is hot, expensive and narrow, and proposes to replace it by a small
> specialized model. It sets up a training and validation environment in a
> fork of the persistent memory (datahike), including external training data,
> fine-tunes a small model (finetune-rstr on raster), and once validation
> accuracy is sufficient the small model is swapped in through the staging
> mechanism. The system keeps monitoring it and falls back to the frontier
> model when quality drops.

The same loop describes a JIT (proposer: specializer; relation evidence plus
admission conditions), AutoML and schedule search (proposer: Bayesian optimization; licence:
measured cost), self-rewriting application code (proposer: an LLM; licence:
tests, proofs, human review), and the predictor ladder of
`doc/architecture.md`. One mechanism, different licences.

**Clarification, 2026-10-29 (S26–S29).** Evidence, assumptions and admission have
different jobs. A theorem establishes a relation under its premises; a guard
establishes premises for an actual execution; tests give empirical confidence;
profiles guide investment. These are not a total strength order. A proof of a
Nat identity, for example, does not by itself license a checked-Long rewrite or
remove its bounds/fallback. The implemented path binds exact endpoints and
dependencies, checks a complete candidate during preparation, and publishes it
after fork exit. Adopting a compiler branch and publishing an executable are
separate operations. See [the current account](../doc/checked-specialization.md)
and [correctness ledger](../doc/engineering/correctness.md) for the bounded implementation and trust
boundaries; the learned-component protocol below remains proposed.

## Proposal

**1. Components with contracts.** A replaceable component is a call site or
definition with a declared contract: an input/output shape and, when exact
agreement is not the goal, an *approximation contract* (`within`, RFC/v2 §7)
with a metric and an observation rule. A component with no contract can only
be replaced under the exact observation contract. Replacing outputs by
approximations requires a declared metric; nondeterminism does not eliminate
the obligation to state which observations a replacement preserves.

**2. The loop.** Every replacement uses the following stages:

```
propose  (fork)     a proposer — specializer, search, LLM — creates a candidate
                    in a fork of the world; budget authority is split to it
ground   (evidence) training, measurement, validation run in the fork;
                    external data enters as evidence with provenance
license  (certify)  a licence of one of the kinds below is produced
adopt    (join)     adopt a completed compiler-branch result at fork exit
publish  (install)  validate current installation conditions and atomically
                    publish a complete executable; policy may decide auto vs review
monitor  (guard)    runtime guards and monitors keep checking; failure falls
                    back to the generic component and may trigger a new loop
```

The intended asynchronous policy can keep using the generic component while a
candidate is prepared. This is a scheduling property, not a consequence of
staging or fork isolation. Current examples explicitly invoke synchronous
preparation and pay its cost; the same preparation program may be scheduled
outside the critical path by a future runtime policy.

**3. Evidence and admission responsibilities**, which may be combined:

| Kind | Responsibility | May remove the fallback? | Typical proposer |
|---|---|---|---|
| proved | a theorem establishes the stated relation/invariant under explicit assumptions, for actual endpoints | only with complete admitted-domain/context coverage and discharged or explicitly trusted semantic bridges | specializer, LLM with proof search |
| guarded | inert admission establishes actual input/world/context requirements before candidate effects | not by itself; guard failure still needs a valid alternative or reference path | JIT specializer |
| tested | property tests or a corpus support an implementation bridge empirically | not by itself; a guard cannot turn a tested rewrite into a theorem | compiler engineering, LLM code edits |
| statistical | held-out evaluation supports a declared approximate contract with stated assumptions | only as that approximate contract permits; not an exact replacement guarantee | training (distillation, estimators) |
| reviewed | an authorized policy accepts a proposal and its stated risks/contract | review alone does not establish semantic equivalence or coverage | any |

S29's immutable value evidence can discharge a consumer's input guard without
rescanning. It does not discharge unrelated current world/handler requirements
or freeze live authority rights. Validation receipts allow publication to reuse
checking of the exact immutable executable; they are not runtime permissions.

Licences compose with the evidence discipline: the data used to train or to
select a candidate is never the data used to claim its quality (selection is
a fork); a statistical licence names its held-out evidence tokens.

**4. Monitors (proposed).** A monitor is a guard with a statistical rule: it samples a
fraction of uses, runs the generic component in shadow (or compares with
labels when they arrive), and fails when the observed metric leaves the
contract (drift detection). Failure may select the generic component for future
calls and optionally start a new loop. It does not retroactively repair already
observed approximate outputs. Shadow execution, cancellation and any restart
need an effect/observation contract that prevents duplicating irreversible
effects. Monitors are effects with their own budget. (Naming: Klara's `esc` is the staging
splice; monitoring hatches get their own name, e.g. `monitor`.)

**5. Concurrency.** Proposals, training and validation run concurrently in
forks with split budgets. Several candidates may compete; selecting among
them is itself evidence-consuming and needs fresh held-out data for the final
claim.

**6. Effects inside the loop.** Training spends budget (GPU time, money):
budget authority (RFC 0001). External API calls and data acquisition inside a
fork are irreversible effects: deferred to adoption or performed under an
explicit capability recorded in the receipt.

## The distillation example, step by step

1. The workflow's call site `classify-ticket` declares a contract:
   input shape, output label set, metric = agreement with the frontier model
   on a labelled sample, threshold 0.95, failure probability 0.01.
2. Receipts show the site is hot and costly; the proposer (a frontier LLM, or
   a planning policy steered by cost models) proposes distillation.
3. `fork` the world: a datahike branch with logged inputs/outputs as training
   evidence, external data imported with provenance, a held-out split sealed
   as claim evidence; budget split from the session.
4. Training: a finetune-rstr job (LoRA on a small model over raster) runs as
   an effectful computation in the fork, under `converge` with estimates.
5. Licence: evaluation on the sealed held-out split; agreement 0.97 with a
   confidence bound above 0.95 → statistical licence naming the evidence.
6. Adopt and publish: accept the completed compiler/training-branch result,
   then install the small model at `classify-ticket` through the specialization
   cache, guarded by an input-distribution guard, generic fallback = the
   frontier model; the proposed acceptance policy may require review.
7. Monitor: 2 % of calls are shadow-evaluated against the frontier model;
   agreement below threshold → fall back, receipt, retrain proposal.

## Alternatives considered

- **Separate MLOps tooling** outside the language: loses forks, provenance,
  guards and the single receipt chain; the same mechanism already exists for
  the JIT.
- **Treat learned components as exact replacements**: unsound; they need an
  approximation contract.

## Obligations and falsifiers

| Id | Obligation | Status |
|---|---|---|
| LS1 | No replacement without a contract and a licence; components without an approximation contract only accept exact licences | Open |
| LS2 | Statistical licences name disjoint training/selection/claim evidence | Open (G9) |
| LS3 | Monitors detect contract violation within a stated delay and fall back without repeating irreversible effects | Open |
| LS4 | The application never blocks on proposal, training or licensing | Open (R1/R2 analogue) |
| LS5 | Deleting all installed candidates changes observations only within the declared contracts (exact components: not at all) | Tested for exact compiler/direct-call subset (S12, R3); general contracts open |
| LS6 | Budget spent by loops is conserved and attributable (receipts) | Open |
| LS7 | Relation evidence transports through specialization under compatible assumptions and observations | The spec proves trivial partial application for closed values (`smn`, `smn-equiv`); bounded mathematical/private/value-fact compositions are checked in S26–S29; general evidence transport remains open |

## Open questions

1. Contract syntax for approximation: extend `within` with metric, threshold,
   failure probability and sampling rule?
2. Default adoption policy per licence kind (auto for proved/guarded; review
   for tested/statistical?).
3. Where the frontier-LLM proposer lives: a Klara effect (`:propose`) whose
   handler is an agent (dvergr), so proposals are forks with receipts.
4. Demo choice: distillation of one call site in a real workflow, or an
   estimator inside a simulation (a surrogate replacing an expensive model
   component under `within`).
