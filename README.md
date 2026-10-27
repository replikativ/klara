# Klara

A Lisp for forkable, inspectable computation: simulation, inference and
certified optimization, hosted on the JVM and embedded in the Clojure
ecosystem. Named after Klára Dán von Neumann, who wrote the code for the first
computerized Monte Carlo simulations on ENIAC in 1948.

**Status: private design draft.** Nothing here is stable; history will be
rewritten before publication.

- `doc/` — design iterations (`00-design-space`, `01-core-v2` is current),
  worked examples, spindel/sci alignment, demo plan; `doc/research/` holds the
  research notes A–H, `doc/reviews/` the external critiques.
- `rfc/` — design RFCs (template, 0001 forks and authority, 0002 effects and
  handlers).
- `experiments/` — measurements backing design decisions (JVM effect-handler
  costs).

Klara is part of the [replikativ](https://replikativ.org) stack. Its calculus
is λ∨ (developed separately). Licensed under the Apache License 2.0; Klara is
written clean-room with respect to Clojure's implementation (see
`doc/00-design-space.md`, "Copyright separate").
