# RFC 0002: Effects and handlers

- Status: draft
- Owner(s): Christian Weilbach
- Experiments: JVM handler cost probe (`klara-proto/handlers`, pending), partial-cps dual-mode branch, spindel await/rebuild, foerster replay
- Obligations: EF1–EF6 below

## Motivation

Inference (`choose`/`observe`), async (`await`), generators (`yield`), world
access, host interop and exceptions are all effects in Klara Core (v2 §1).
Three problems need a design:

- **Accidental handling**: with dynamic deep handlers, an operation can be
  caught by an unrelated handler installed by a library in between.
- **Cost on the JVM**: there are no first-class continuations; general
  handlers need CPS or heap frames, which must not tax code that never
  suspends.
- **Multi-shot** resumption for inference cannot clone JVM frames.

## Proposal

1. **Two kinds of handlers.** *Lexical handler instances* for user-defined
   effects: `handle` binds an instance (a capability value), and `perform`
   targets that instance explicitly. *Dynamic handlers* for ambient effects
   (`:world/*`, `:host/*`, `:time`, `:exn`), installed by the runtime or the
   embedding platform.
2. **Operation classes.** Each operation is declared *tail-resumptive* (resumes
   once, in tail position: state, reader, logging, weight accumulation),
   *abortive* (never resumes: exceptions, early exit) or *general*.
   Tail-resumptive and abortive operations compile to direct calls.
3. **Dispatch erasure by staging.** When a region's handler context is known
   at specialization time (binding-time grade S, or A with a guard checked on
   region entry), the region is specialized per handler context and its
   `perform`s become direct calls. Fallback on guard failure: replay from the
   region entry (live frames cannot be converted later). This reaches
   Effekt's static result (Schuster, Brachthäuser, Ostermann, ICFP 2020) by
   staging instead of types.
4. **General operations** run in regions compiled with selective CPS
   (partial-cps) or explicit heap frames. A host frame between capture and
   handler is an opaque boundary: a tested error, not silent misbehaviour.
5. **Multi-shot** = fork-resume (RFC 0001): branch the store, split
   authorities, resume the CPS continuation (compiled regions; 1.65× a
   hand-written search on exact enumeration) or re-execute from a savepoint
   behind opaque host frames (spindel rebuild, foerster replay; 4.6–15×
   slower). Allowed only when the captured computation's authorities can be
   split.

## Alternatives considered

- **Dynamic deep handlers only** (v1): simpler, but accidental handling and no
  common-case erasure.
- **A static effect type system** (Koka, Effekt): the strongest static
  guarantees; contradicts the untyped core; kept as an opt-in narrowing layer
  ("typed Klara effects").
- **Loom continuations** (`jdk.internal.vm.Continuation`): works on JDK 25
  but internal, one-shot only, and measured at 250 ns per perform (≈20× the
  CPS path); rejected.
- **Evidence passing everywhere** (Koka, Xie & Leijen ICFP 2021): the model
  for lexical instances; full adoption needs types for its optimizations.

## Obligations and falsifiers

| Id | Obligation | Status | Check / falsifier |
|---|---|---|---|
| EF1 | Tail-resumptive `perform` within 2× a protocol call | Holds (1.18×, ≤2 clause types per site; 7.7× at 3) | handler probe |
| EF2 | An installed but unused handler frame costs ≈ nothing | Holds (install ≈11 ns); but CPS-compiled code is 2.7× slower even when no perform fires | handler probe |
| EF3 | Erased regions produce identical traces to generic regions | Conj | differential tests; guard failure replays without repeating effects |
| EF4 | Lexical instances prevent accidental handling | Conj | adversarial composition tests (library handler in between) |
| EF5 | Opaque host boundary is detected, never silently wrong | Conj | Klara → linked Clojure → callback → effect test |
| EF6 | Fork-resume by replay is deterministic | Holds in spindel (S2, S6) | port tests |

## Compatibility

L0/L1: Clojure code performs no Klara effects; exceptions map to `:exn`.
L2: `defeffect`, `handle`, `perform` are new names; `await`/`yield` are
library operations over them.

## Open questions

1. Region granularity for dispatch erasure: per function, per loop, per
   staged region? (Jonathan Brachthäuser: experience from Effekt's
   capability-passing compilation and the 2018 Java work.)
2. Do we need a typed effects layer in v1, or is dynamic checking plus staging
   enough for the first users?
3. The shared effect-handlers benchmark suite has no JVM entry — contribute
   Klara's? (joint with Effekt)
