# Bounded Code inspection and structural generation

This milestone connects guest generators to existing closed Code, using the
same scoped term representation as ordinary staging. It adds three operations,
not another compiler IR or a benchmark-specific generator:

```clojure
(perform :stage/inspect source)
(perform :stage/rebuild cursor child-codes)
(perform :stage/compose cursor template argument-codes)
```

The [implementation](../../src/klara/compile/view.clj),
[guest walkers](../../examples/compat/klara/residual.cljc) and
[regressions](../../test/klara/compile/view_test.clj) state the current boundary.

## Interface and scope contract

Inspection accepts closed Code in the finite `quote/var/fn/let/if/letrec/app/
prim/resolve` fragment. It returns `:source-id`, a `:root` index and a vector
of node descriptions. Each description contains:

| Field | Meaning |
|---|---|
| `:at` | Opaque cursor carrying the original node, lexical permissions and allowance |
| `:code` | Original fragment, possibly open when extracted from under a binder |
| `:op`, `:children` | Existing term operation and ordered child indices |
| `:bindings` | Integer labels introduced by this node |
| `:binding` | Referenced label, for a variable |
| `:scope` | Labels available at this node |
| Other descriptions | Literal datum, primitive/global name, function arity/rest flag |

Labels are local to one inspection. They let analyses distinguish variables
and binder groups without exposing binding tokens or granting construction
authority. The cursor remains authoritative: changing a description's `:op`
or `:bindings` does not change the node it rebuilds.

Rebuilding retains that node's operation and binders. Its Code children must
fit the original child positions and lexical scopes. A closed replacement is
allowed; an open fragment referring to a different function's parameter is
rejected. Extracting an open fragment does not make it runnable.

Inspection first bounds and checks the input, then alpha-refreshes every binder
occurrence through the existing closed Core conversion. This matters when one
Code value is spliced twice: its two binder occurrences must not become a
channel for moving an open body from one sibling into the other. The regression
explicitly exercises this case. Quoted data remains opaque syntax.

Current maximums are 512 syntax nodes, depth 64, 20 names per binder group and
32,768 counted work units per view. Options may lower these limits. Inert literal
data uses the restricted compiler-service data domain (including scalar values,
vectors and maps); arbitrary host objects and other literal classes decline.
Effects and nested staging syntax are outside this first inspection fragment.
Inspection and all cursors from it share an allowance; failed rebuilding does
not refund prior work. Fixed traversals, allocation and primitive latency do not
turn these counters into exact CPU or wall-clock bounds. The surrounding guest
walker itself is ordinary T0 code, not automatically fuel-limited by this API.

Cursors are temporary job capabilities containing a mutable work counter. They
are not serialized compiler state or proof receipts. Store Code/provenance and
re-inspect after restore rather than treating a cursor as a durable artifact.

## Guest generators

`klara.residual/regenerate` recursively visits descriptions and invokes the
generic rebuilder. It has no arithmetic-loop cases. Tests cover bindings,
branches, collection constructors, unknown function arguments and mutually
recursive local functions. The latter regenerate and run in T0 even though
native emission of their recursive group still declines.

`prune-literal-branches` adds one conservative rule: for an `if` with a literal
test, keep the selected branch using Klara truthiness (only nil/false are
false). The walker never evaluates arithmetic while rewriting. A latent
division-by-zero in the other branch therefore stays unexecuted. It performs
no general constant folding or automatic let motion.

With the normal guest nREPL and `examples/compat` as a source root:

```clojure
(require '[klara.residual])
(require '[klara.compiler])
(def original
  (code (fn [x]
          (if false (/ 1 0)
            (let [y (+ x 1)] (* y y))))))
(def rebuilt (klara.residual/regenerate original))
(def simplified (klara.residual/prune-literal-branches original))
(def kernel (run original))
(klara.compiler/prepare-code rebuilt)
(kernel 4) ; => 25
((run simplified) 4) ; => 25
(def incremented
  (klara.residual/postprocess original (code (fn [result] (+ result 1)))))
((run incremented) 4) ; => 26
```

Identity regeneration preserves the original CoreID, allowing its prepared
candidate to accelerate the original entry. Literal pruning changes CoreID.
Preparing that rewritten Code does **not** silently replace the original
function: a semantic replacement needs a checked source/residual relation.
Scope-safe rebuilding alone does not provide it.

`postprocess` deliberately creates a different function. Its closed template
gets fresh binders and receives the original body as a once-evaluated argument.
The [composition regressions](../../test/klara/compile/compose_test.clj) cover
capture rejection, argument ordering, unused arguments and shared allowances.

## Correctness work remaining

The current evidence is bounded validation, per-artifact source identity and
regression tests. No new universal ansatz theorem is claimed. The next focused
model result should establish, for the admitted closed fragment:

1. Inspection/alpha-refresh preserves Core, modulo debug metadata.
2. Scope-admissible children rebuild a scope-admissible parent.
3. Generic identity regeneration preserves decoded Core structurally.
4. Literal-branch pruning preserves the chosen observations, including failures
   and evaluation order, under the language's truthiness rule.

The model-to-host conversion and backend remain explicit tested bridges.
Termination of a traversal alone is insufficient: these are binding and
semantic correspondence obligations.

The builder also supports a bounded composition operation: a closed,
fixed-arity function template and a vector of argument Code become ordered
`let` bindings followed by the template body. Template binders are freshened;
arguments must fit the cursor's original scope. Every argument is evaluated
once, left to right, even if unused or referenced repeatedly by the body.
The operation constructs Code without executing it. The guest `postprocess`
example uses this to wrap a function body.

This is an ordered-let construction contract, not a theorem authorizing
replacement of arbitrary closure calls. Global references, closure/world
context, effects and failures still need semantic correspondence evidence.
See [bindings and modules](bindings-and-modules.md) for the distinction between
lexical scope safety and module/phase hygiene. General beta-reduction,
effect-aware motion and rewriting existing world definitions need further
interfaces and obligations. General analysis can use the read-only
binding/child labels; facts it proposes must still be justified by guards or
proof before lowering consumes them. The walkers currently run in T0, not as
an already efficient self-hosted compiler.

## Reproduction

```sh
clojure -Sdeps '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}' -M -m consolidation.code-view
clojure -M:test
clojure -M:verify
```

The [recorded scenario](../../experiments/consolidation/code-view-results.edn)
retains source fingerprints, Core identities, the pruned form, a rejection and
execution through the original installed entry. New output goes under `target/`.
The original inspection milestone passed 234 tests / 7,005 assertions.
After ordered composition and the literal/local-call refinements, aggregate
checks in the existing host REPL pass: 249 tests / 7,175 assertions and
verification 144 tests / 3,511 assertions. These are implementation results, not the model
theorems listed above.
