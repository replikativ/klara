# Klara — worked examples, seams, non-goals (iteration 0, 2026-10-27)

Six programs Klara exists for, written in a provisional surface syntax and
traced through `01-core-v1.md`. A feature no example uses is a candidate for
removal; a step no example can express is a gap (**G1–G13**, collected in §2).
The syntax is illustrative, not a proposal for the final surface.

## 1. The examples

### E1. Sequential Monte Carlo with resampling

```clojure
(defmodel hmm [ys]
  (loop [x (choose :x0 (normal 0 1)) t 0]
    (if (< t (count ys))
      (let [x' (choose [:x t] (normal x 1))]
        (observe [:y t] (normal x' 0.5) (nth ys t))
        (recur x' (inc t)))
      x)))

(smc hmm data {:particles 1000 :resample :systematic})
```

Trace. `choose`/`observe` are `perform`s; `smc` is a handler running one fiber
per particle. `observe` accumulates a weight (evidence sort, linear). The
address `[:y t]` is the linear token: each address is observed at most once
per trace (λ∨'s footprint discipline). Resampling forks particles: state is a
value (copy), the random key is split, the continuation is copied, which is
legal because it captures no resource (§1, multi-shot rule). The first write
to a forked particle's state copies the touched path (JVM region tokens:
every child copies, B §0.4).

- **G1 — resampling is not a per-particle split.** Systematic resampling turns
  a parent of weight w into k children of weight W̄ each; k·W̄ ≠ w in general.
  Mass is conserved only across the population. Resampling is a collective
  operation: join all weights, then split the pooled mass. The evidence sort
  needs a population-level rule ("join, then split"), not only a per-object σ.

### E2. The city: close a shopping centre, compare with common random numbers

```clojure
(with-ledger
  (fork :coupled [w (scenario/close city :milaneo)]
    (within {:rel 0.01}
      (delta (spending city :mitte) (spending w :mitte)))))
```

Trace. The world is branchable: `fork` performs `branch!` (snapshot meaning,
Q4). `:coupled` shares random keys across both sides, so the difference
measures the intervention, not noise (Q6). `spending` is heavy: the mapper
translates it to the GPU (a `translate` receipt with measured ε and cost);
`within` lets the policy pick a fidelity (e.g. multilevel Monte Carlo levels)
whose declared error meets 1 % relative; `with-ledger` collects receipts.

- **G2 — fork results and settlement.** What does `fork` return, and when is
  a branch settled (adopted or discarded)? Proposal: `fork` returns the branch
  results as values; branchable resources are discarded at scope exit unless
  explicitly adopted (`adopt!`), so settlement-exactly-once is automatic.
- **G3 — metrics for `within`.** A relative error on a number is clear; on a
  map, a distribution or network weights it is not. Each type used under
  `within` needs a declared metric (a protocol `distance`), and a missing
  metric is a static or dynamic error, never a silent default.

### E3. The REPL: redefine notation under a running simulation

```clojure
(defsyntax twice [e :expr] `(+ ~e ~e))
(defn f [x] (twice x))
(def sim (spawn (run-sim city f)))     ; fiber with a pinned basis
(defsyntax twice [e :expr] `(* ~e ~e)) ; new world; f re-expands lazily
(raise-basis! sim)                     ; sim sees the new f from its next safe point
```

Trace. C §4.3: the redefinition writes a new world; `f`'s recorded expansion
read of `twice` marks it dirty; on demand it re-expands, the output hash
differs, `f` is re-analyzed. `sim` keeps the old `f` until it raises its basis.
This is exactly experiment X1.

- **G4 — safe points.** A basis raise must happen at a well-defined point: at
  a handler boundary, between iterations of an `:iterate`, or at a fiber
  yield — never in the middle of a function body. The design needs a
  definition of safe points (as JIT deoptimization does).
- **G5 — grammar declarations.** `[e :expr]` is the syntax-extension
  interface (§13). The set of syntax classes (`:expr`, `:binding`, `:body`, …)
  is a small standard library that must be designed with the expander.

### E4. Interop: a linked JSON library and a hosted pricing library

```clojure
(require '[cheshire.core :as json])         ; linked: plain Clojure
(require-hosted '[shop.pricing :as p])      ; hosted: defs in the world, forkable

(fork [w world]
  (p/quote (json/parse-string body true)))
```

Trace. `parse-string` returns a Clojure persistent map: a value by the class
allowlist. cheshire's internal state is shared by all forks (linked, Q12).
`shop.pricing` was expanded by Klara, so its definitions live in the world
and fork with it.

- **G6 — deep value-ness.** A Clojure map may contain a `java.io.File`, an
  atom or a Java object. Whether the map is a value depends on its contents,
  and Clojure's collections have no spare field to cache a bit. Options:
  shallow classification plus a cached deep check at fork boundaries (cost
  O(n) on first fork, cached in a weak identity map), or "trust at Tier H".
- **G7 — lazy sequences are everywhere.** `map`, `filter`, `for` in linked
  code return lazy seqs, which D §4.4 classifies as resources (a locked memo
  thunk). If that rule is applied literally, forking nearly any Clojure data
  is forbidden. Proposal: treat a lazy seq as a value under the Clojure
  convention that seq thunks are pure (documented Tier H assumption), and
  offer `realize` / strict variants where purity matters.

### E5. Training as convergence, with two strategies

```clojure
(converge sgd-step θ0
  {:spec       (fn [θ] (< (val-loss θ) 0.1))
   :budget     {:time-s 3600 :money-eur 20}
   :strategies {:adam adam-step :sgd sgd-step}
   :fork       :coupled})
```

Trace. `converge` performs `:iterate`; the policy handler runs both strategies
as speculative forks, coupled so that both see the same minibatches (Q6 pays
off: a fair comparison). Each step yields a receipt with a predicted ε_n
(licence: predicted). The handler stops a strategy when its expected
improvement is worth less than its cost, and joins by value: selecting the
winner is a fork (ESOP), so the reported loss must come from data not used for
selection.

- **G8 — budget objects.** The budget is split across strategy forks (σ on a
  budget vector with hard components: time, memory; traded components:
  money, energy — Q15). Budgets need a representation and a split rule.
- **G9 — held-out discipline.** "Selection evidence ≠ claim evidence" must be
  enforceable: the validation set used for stopping must be a different
  evidence token from the one used for the reported result.

### E6. An agent experiment on an existing system

```clojure
(with-branch [conn' (branch! conn)]          ; datahike connection: branchable
  (d/transact conn' (agent/propose-migration schema))
  (let [report (check-invariants @conn')]
    (when (:ok report)
      (propose! conn' report))))              ; adoption goes through review
```

Trace. The datahike connection is branchable; the transaction affects only the
branch; `propose!` hands the branch to the adoption boundary (Simmis review)
with its receipts; unadopted branches are discarded at scope exit.

- **G10 — irreversible effects inside forks.** What happens if code inside a
  branch sends an email or calls a payment API? The design has no rule. This
  is the most important gap. Proposal: effects are classified *reversible*
  (on branchable resources) or *irreversible* (host I/O). Inside a fork,
  irreversible effects are by default *deferred* to adoption (queued as
  intents and executed only if the branch is adopted), and may be performed
  directly only with an explicit capability, which is recorded in the
  receipt. Simmis already draws this line (PRODUCT.md: "irreversible external
  actions need separate controls").

## 2. Seams (gaps from the examples plus the ones known before)

| # | Seam | Proposed direction | Status |
|---|---|---|---|
| G1 | Resampling is collective, not per-particle split | evidence rule "join then split" for populations | Open |
| G2 | Fork results and settlement | branch results are values; scope-exit discard; explicit `adopt!` | Proposal |
| G3 | Metrics for `within` | `distance` protocol per type; missing metric is an error | Proposal |
| G4 | Safe points for basis raises | handler boundaries, iteration boundaries, fiber yields | Proposal |
| G5 | Syntax classes for extensions | small standard set, designed with the expander | Open |
| G6 | Deep value-ness of host collections | cached deep check at fork, or Tier H trust | Open |
| G7 | Lazy seqs from linked code | value by Clojure purity convention, `realize` when needed | Proposal |
| G8 | Budget objects | budget vector, hard vs traded components, σ-split at forks | Open |
| G9 | Held-out discipline | distinct evidence tokens for selection and claims | Proposal |
| G10 | Irreversible effects in forks | reversible/irreversible classification; deferred intents; capability to act | Proposal (most important) |
| G11 | Inspecting evidence at the REPL | read-only borrow for printing and debugging; does not consume | Proposal |
| G12 | Handler cost on the JVM | measured by the handler probe (klara-proto/handlers) | Running |
| G13 | ESOP join as a library | the four declarations (base, identification, weights, residual) as arguments of a `join` over core + handlers; if not expressible, a primitive is missing | Open (to check) |

## 3. Clojure's special forms into Klara Core

| Clojure | Klara Core | Fits? |
|---|---|---|
| `def` | `(perform :world/define id v)` | yes |
| `if`, `quote` | `if`, `quote` | yes |
| `do` | `let` chain | yes |
| `let*` | `let` | yes |
| `loop*` / `recur` | `letrec` with a self tail call; the spec must guarantee constant space for these calls (the JVM has no general tail calls, so loops compile to jumps) | yes, with a spec obligation |
| `fn*` (multi-arity, variadic) | `fn` with fixed arity; arity dispatch and rest arguments elaborate through `prim` | yes, minor |
| `letfn*` | `letrec` | yes |
| `case*` | `if` + a `prim` jump table (keeps O(1) dispatch) | yes |
| `throw`, `try`/`catch`/`finally` | `:exn` effect; `catch` matches a class predicate; `finally` needs an unwind-protect handler | yes, needs unwind semantics |
| `var` | `(perform :world/ref id)`: a reified identity | yes, reflective |
| `set!` on vars | `:world/set` within a dynamic-scope handler | yes |
| `binding` (macro) | dynamic-scope (reader) handler; conveyance into forks and fibers must be specified | **resists**: conveyance rules |
| `new`, `.` | `(perform :host/new …)`, `(perform :host/call …)` | yes (Tier H) |
| `set!` on mutable `deftype` fields | the object is a resource; `:host/field-set` | **resists**: mutable fields make the type a resource |
| `deftype*`, `reify*` | emitted JVM classes (Tier H); Klara-native types via `defop`/`defshape` | yes (Tier H) |
| `monitor-enter`/`monitor-exit`, `locking` | `:host/lock` on a resource; forbidden inside forks unless the lock is fork-local | **resists** |
| `import*` | namespace effect | yes |

The resisting forms are the ones that expose shared mutable state: dynamic
binding conveyance, mutable fields, and locks. They stay Tier H with documented
fork behaviour; none needs a new core form.

## 4. Non-goals for v1

- No typed surface language; types are opt-in claims.
- No distributed arrays, sharding syntax or user-visible schedule language
  (raster's plan IR is reached through `translate`).
- No promise that arbitrary Clojure code behaves identically under forks
  (linked code is outside the guarantees).
- No owned runtime before 2027; the JVM is the v1 host.
- No compatibility with Clojure's internals (compiler, `clojure.lang` classes
  beyond their public interfaces).
- No general optimality claim for allocation policies (metareasoning is
  intractable in general); only invariance, conservation and known instances.
- No backup cycle collector on owned runtimes in v1.

## 5. Size budget

Target: the core semantics fits on two pages (as Wasm's core and R7RS-small
do). Currently: 12 forms, 5 reference handlers, 4 sorts. Each new form or
handler must be justified by an example above; the rule count will be checked
when the ansatz specification (X3) exists.

## 6. What the examples changed

1. **G10 (irreversible effects in forks) is a missing core concept**, not a
   detail: the reversible/irreversible effect classification and deferred
   intents belong in 01-core-v1 §2 next to the sorts.
2. **G1 shows evidence needs collective operations** (population join then
   split), which also matches the ESOP paper's apportioning at the fork.
3. **G6–G7 show the interop boundary is about contents, not classes**:
   value-ness of host data must be decided per object graph, with a pragmatic
   Tier H default.
4. Every example uses fork, effects and receipts; none uses `specialize`
   directly (it appears only inside the runtime). Keep it in the core for the
   s-m-n law, but it is not user-facing in v1.
