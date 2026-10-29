# Design objectives

Klara is an independent language project for self-organizing and self-optimizing
systems, unifying the replikativ work in a common programming model. It aims to
make the running system its own development and optimization environment.
Programs, compiler components, analyses and learned policies should
be inspectable, versioned values that can evolve while existing computations
retain a coherent world. The long-term ambition is a programming model for
general-purpose learning and autonomous program improvement, including AGI.
The concrete objectives below are how we intend to make that ambition useful
and assessable. [STATUS](../STATUS.md) records what works today.

## Persistent development worlds

Code, application data and compiler state should share a persistent memory
model. A fork can explore a rewrite, train a predictor, construct a proof or
run tests without publishing its changes to the application. Accepted changes
can be validated and published while older activations retain their basis.
Authority and external effects need explicit protocols; immutable memory alone
does not make arbitrary host code safe to speculate.

Current world roots use Clojure persistent maps. We expect durable storage to
build on Datahike and other replikativ persistence libraries, potentially
including Geschichte for version history and collaboration. These adapters
are planned. The current deployment bundle is a restricted source/Core/data
format, not that shared durable store.

## Live development with reproducible source and deployment

We want the convenience of a live image together with explicit, reviewable
source and reproducible deployment. This addresses the source/image tension
that motivates the comparison with Smalltalk: a running system should be
inspectable and evolvable, while selected code and state can be projected into
files and databases, versioned, frozen and deployed deliberately.

Definitions already retain source forms and expanded Core. The deployment API
can project retained source for inspection and restore supported worlds/data
in a compatible fresh JVM without replaying data initializers. Its Core/data
manifest is authoritative. This is not yet a general inverse from arbitrary
runtime values or generated machine code to faithful source files.

The stronger objective is to resume computations and compiler jobs from
explicit safe points, eventually from any modelled suspension point. That needs
a versioned representation of continuations, compiler progress, host resources
and authority settlement. The current bundle declines live continuations,
authority, captured/pinned closures and opaque mutable state. It cannot resume
an arbitrary process at an arbitrary machine instruction.

Snapshots should support retaining detailed provenance or consolidating it
under an explicit policy. Consolidation must state which history and audit
observations it preserves and what it discards, while retaining dependencies
and proof evidence needed by surviving code. We have source/generation IDs and
evidence records, but no general provenance-compaction or snapshot-GC protocol.

## Programmable learning and optimization

Staging should let ordinary programs construct and improve their own analyses
and compilers. Startup analysis, runtime profiling and later recompilation
should invoke the same specialization machinery with different available
facts. Profiles and predictions guide investment; checked assumptions and
semantic evidence justify accepting the result.

The bounded [guest planner](../examples/staging/15-planned-jit.klr) already
selects checked numerical/fusion/private-memory recipes and can evolve in a
policy world. Its costs are supplied estimates. The separate
[speculative pipelining example](../examples/staging/16-learned-speculation.md)
updates a predictor during operation and overlaps an admitted follow-up with
its producer. The original benchmark's learner/orchestration are hosted in
Clojure; the teaching prototype moves prediction, learning and staging into
Klara. Combining these into a general learned guest optimizer remains work.

## Operation, accounting and investment policy

Optimization is itself an investment by the running application. Klara aims
to bring operation, resource accounting and investment policy into the same
programming model: a computation can measure costs, allocate a budget, explore
alternatives, evaluate expected benefit and update its policy from outcomes.
Costs may include latency, CPU, retained memory, energy or external service
charges. Their values and trade-offs belong to the application; they need not
all be reduced to money.

Resource limits, measured charges and profitability forecasts have different
roles. Limits bound authorized expenditure; measurements record what happened;
forecasts estimate whether future savings justify preparation, training,
validation and potentially duplicated work. Safe speculation can be a poor
investment. Autonomous applicability therefore needs a policy that can decline,
probe under a budget and adapt to changed workloads, while semantic admission
continues to check correctness independently.

The prototype has authority/budget mechanisms, measured investment charges,
benchmark cost components and a planner with supplied estimates. It does not
yet provide comprehensive resource metering or a calibrated, autonomous
profitability controller. This integration of operational economics is an
objective, not a claim that a complete business/accounting system is built in.

Several further objectives follow:

- **Application-defined value:** latency, throughput, memory, energy, service
  charges and output-quality contracts can have different priorities in
  different contexts. Policies should respect explicit constraints and units;
  there need not be one universal scalar score or monetary objective.
- **Honest settlement:** reserving resources, consuming them and returning
  unused reservations are distinct operations. Discarding a speculative world
  must not erase the cost of work already performed or duplicate spending
  rights. Receipts should identify the responsible job, policy and code world.
- **Learning with attribution:** record preparation, monitoring, retention and
  losing-work costs as well as successful latency savings. Comparing a
  candidate with a baseline needs a stated workload and measurement contract.
  Estimates need uncertainty and drift handling; bounded exploration can be
  worth funding even when immediate benefit is uncertain.
- **Coordination across jobs:** local optimizers compete for shared workers,
  memory and budgets. A policy that helps one request can harm system
  throughput. Scheduling and investment should account for this opportunity
  cost rather than having every component speculate independently.
- **Improving the improvement process:** choosing an analysis, proof search,
  compiler pass, training run or agent proposal is itself a program subject
  to costs and budgets. Replacing that policy can use the same world and
  admission mechanisms, with a bounded top-level policy preventing endless
  investment in meta-optimization.

This makes self-organization concrete: a system should adapt how components
cooperate and receive resources, as well as how individual functions compile.
Persistent worlds supply stable alternatives; contracts and authority govern
what changes are permitted; accounting and learning guide which alternatives
are worth exploring. A complete shared protocol for this remains to be built.

## Agent-assisted program evolution

This boundary should also support coding agents: an agent can propose changes
to application or optimizer code in a fork, produce proofs where supported,
run tests and measurements, then submit a candidate for admission. Proofs have
declared scopes; tests provide empirical evidence. Neither an agent nor a
learned policy should acquire the ability to choose a permissive checker or
silently weaken the application's contract. General agent isolation and an
automated codebase-consolidation protocol are objectives, not current features.

## Clojure compatibility and eventual self-hosting

Clojure source compatibility and practical ecosystem interoperation are goals.
The prototype supports a subset with explicit semantic differences and a host
boundary; it is not a drop-in implementation of all Clojure programs. Shared
host mutation and arbitrary Java interop require their own contracts. The
[interop guide](guide/07-clojure-interop.md) explains the current boundary.

Over time, compiler builders, analyses, policies and lowering passes should
move from Clojure into Klara. We want a self-hosted system that can recompile
its own layers from inside a running world, with the host interface and trusted
checking boundary stated explicitly. Migrating a policy is already demonstrated;
the expander, most analyses, interpreter, validator and emitter remain hosted.

The target model extends beyond the JVM to JavaScript, native code and other
useful substrates. Dedicated emitters and a small host contract should let
Klara generate primitive loops and suitable low-level representations itself.
World, staging and authority semantics must remain coherent across targets.
Today only the JVM host is implemented; the current Clojure/JVM emitter still
relies on the host VM for machine-code generation.

For the proposed architecture and outstanding correctness obligations, see
[architecture](architecture.md), [checked specialization](checked-specialization.md)
and the [RFC index](../rfc/README.md).
