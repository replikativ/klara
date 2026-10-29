# Proof-licensed staged rewrites

This isolated experiment composes a polynomial rewrite with a stream rewrite.
Klara generates the actual source and candidate code. Ansatz checks an equality
between mathematical interpretations reconstructed from those endpoints. A
separate conservative bound checker licenses checked Long evaluation on a guarded
domain. The trusted/tested interpretation bridge is explicit; this is not a proof
of T0 or the JVM compiler. See [the design note](../../doc/engineering/correctness.md).

Run from the repository root, using the current sibling ansatz checkout without
changing Klara's dependency pin:

```sh
clojure -Sdeps '{:aliases {:proof {:extra-paths ["experiments/proof_staging"] :override-deps {org.replikativ/ansatz {:local/root "../ansatz"}}}}}' -J-Xmx3g -J-Xss16m -J--enable-native-access=ALL-UNNAMED -M:proof -e '(require (quote proof-staging-test)) (let [r (clojure.test/run-tests (quote proof-staging-test))] (System/exit (+ (:fail r) (:error r))))'
```

The code works as an ordinary REPL library:

```clojure
(require '[proof-staging :as p])
(def proposals (p/proposals [1 2 3]))
(def domain {:max-x 1000000 :max-count 1000})
(def numeric
  (p/numeric-edge (:source proposals) (:numeric proposals) [1 2 3] domain))
(def stream
  (p/fusion-edge (:numeric proposals) (:both proposals) domain))
(def both (p/compose numeric stream))
(p/run-selected (:source proposals) [both] [1 2 3]) ; 57
```

`polynomial.klr` supplies ordinary user-level numeric and stream code builders.
The two numeric builders can be passed to either stream builder. The result has
four combinations: expanded/map, Horner/map, expanded/fold, and Horner/fold.
The final code contains 17 nodes, compared with 21 in the initial code; this is a
syntax-size observation, not a speedup measurement.

`checked-edge` accepts a proof term, re-elaborates both closed Code values, and
strictly kernel-checks that exact proposition. It checks both arithmetic trees,
including partial n-ary results and the total fold bound, then issues an opaque
edge. `compose` checks intermediate code identity, intersects the domains, and
rechecks an `Eq.trans` proof. `select` accepts alternatives with one source and
chooses the first admitted edge. Ranking can change without changing the checker.
Input-domain failure uses the original source. Relevant active dynamic handlers
or changed host primitive roots cause explicit refusal before evaluation.

The admitted input is an exact `clojure.lang.PersistentVector` of bounded,
nonnegative `Long`s. No lazy/custom sequence traversal, world references, arbitrary
effects, subtraction, source callbacks, native execution, or cache publication is
licensed. `run-code` is the unguarded reference entry for the harness; use
`run-selected` for candidate execution. The executable bound checker is trusted,
not itself a kernel theorem. Host reflection and modification of the checker are
outside the boundary, as with S23's prepared values. Changes racing after a host
root check are also outside this isolated harness; a production integration needs
the runtime's stable host-entry assumptions.

Validation on 28 October 2026: **9 tests, 125 assertions, zero failures/errors**.
The suite checks exact endpoint binding, wrong coefficients/proofs, fresh staged
names, composition mismatches and domain intersection, three optimization choices,
27 coefficient families, arithmetic/fold boundaries, generic fallback, opaque
stages, active handlers, and altered Clojure helper roots. It includes the
counterexample where the expanded polynomial overflows at `x*x` even when its
coefficient is zero, while Horner evaluation would return normally.

The recorded run used ansatz
`5a7f01a60c7a64a0954135f2d5cb998305e397da` and Clojure 1.12.4. The bundled
4,413-declaration Init environment was loaded in **TRUST mode**; newly constructed
proofs were kernel checked. The captured immutable environment is used for every
edge check. Imported theorem statements and their provenance remain part of the
trusted base. `prove-laws!` initializes ansatz's global session, so use a dedicated
proof worker when composing it with other session users.

`ring_probe.clj` records a separate tactic failure at that revision. Its source
SHA-256 was `13f87ea1e3376758156a2f7b2a1388af5af7fbe8ebb7a2fa15c6790ca2a67292`.
The symbolic ring probe hit a `ClassCastException` in `poly-normalize` at line 111;
the implementation also lacked a general non-ground certificate producer. The
prototype uses checked algebraic lemmas and a successful `grind` proof instead.
These are revision-specific observations, not assertions about later ansatz builds.

The isolated symbolic-ring port at `7dd07f6` subsequently passed an independent
consumer check of this theorem and the composition suite. See
[ring validation](ring-validation.md) for the exact revision, commands,
kernel recheck and negative tests, and imported-bundle trust boundary.
The same checks also passed against merged commit `2191c027`; see the separate
[merged-revision validation](ring-validation-final.md).
