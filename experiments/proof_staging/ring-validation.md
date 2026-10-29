# Independent validation of the symbolic ring port

On 28 October 2026, the isolated ansatz checkout at
`7dd07f60d30598e9feb06a575339a0fb689a69a1` passed the exact original Klara Horner
probe, independent strict kernel rechecking, a false-identity rejection test, and
the existing proof-staging suite. This is a new result; the earlier findings for
`5a7f01a` in the README and S24 note are unchanged.

## Command and inputs

Run from the Klara repository root:

```sh
git -C /tmp/ansatz-ring rev-parse HEAD
git -C /tmp/ansatz-ring status --short
clojure -Sdeps '{:aliases {:ring-validation {:extra-paths ["experiments/proof_staging"] :override-deps {org.replikativ/ansatz {:local/root "/tmp/ansatz-ring"}}}}}' -J-Xmx3g -J-Xss16m -J--enable-native-access=ALL-UNNAMED -M:ring-validation -m ring-validation
```

One fresh JVM ran both suites and exited with status **0**. Klara's dependency
pin and sibling repositories were not modified. The runner is
[`ring_validation.clj`](ring_validation.clj). It loads the unmodified
[`ring_probe.clj`](ring_probe.clj), whose exact theorem is:

```clojure
(a/theorem KlaraExperiment.ring-probe
  [a :- Nat, b :- Nat, c :- Nat, x :- Nat]
  (= Nat (+ a (+ (* x b) (* (* x x) c)))
         (+ a (* x (+ b (* x c)))))
  (ring))
```

The checkout reported only an untracked `classes` symlink, pointing to
`../ansatz/classes`. The CLI warned about that
external classpath path. This was a source-and-bundle override using the available
compiled Java kernel, not a clean rebuild of all Java classes or a published JAR
validation. The relevant fingerprints were:

| Input | SHA-256 |
|---|---|
| `src/ansatz/tactic/ring.clj` | `6af247442564cf29bdf4b9616691610632ce3486fe51f20be01544c43f3ed830` |
| `resources/ansatz/init-medium.ndjson.gz` | `354a88d3b443c3d127becd6ddd72ce7d284dea105512f2cf1ef276ce8dce8ef7` |
| `resources/ansatz/bundle.edn` | `71372a4fdbd0b263d673a6537c0b51bf09a99e074ce73614d1708cb38efeb3e7` |
| `classes/ansatz/kernel/TypeChecker.class` | `3df16726bdfca973861b0e4f53787b9da53ad3ebc73e314f3900351820bc9677` |

## Observed results

The exact theorem succeeded with `(ring)`. The runner then extracted its closed
proof and statement from the immutable environment and called
`ansatz.kernel.env/verifies?` independently. That API performs strict
`checkConstant` checking of the supplied proof against the supplied goal; the
test did not merely trust tactic completion or use lenient type inference.

The extracted proof references `Lean.Grind.CommRing.eq_normS` and does not cite
its own theorem name. Independent checking returned **true**. Supplying that
same proof against the original theorem with its right-hand side increased by
one returned **false**. Asking `(ring)` to prove that false symbolic identity
also failed with `:kind :tactic-error` and left the environment unchanged; no
false theorem declaration appeared.

Relevant output:

```text
Ansatz: loaded the bundled medium Init tier (5117 declarations, TRUST mode).
✓ KlaraExperiment.ring-probe proved
:ring-proof {:declarations 5118,
             :kernel-accepted true,
             :changed-endpoint-rejected true,
             :goal-sha256 0eb63801e5974020c926628479d3a4f2fdd1bec73dda8c130d469f5eab521603,
             :proof-sha256 d7aa724975ea3e6d568c0ff28a9770792c7fe110ce37307912369665a12b2884}
:false-ring-identity {:status :rejected,
                      :kind :tactic-error,
                      :message ring: polynomial normalization could not certify the equality}

Ran 1 tests containing 10 assertions.
0 failures, 0 errors.

Testing proof-staging-test
✓ KlaraExperiment.horner proved
✓ KlaraExperiment.horner-grind proved
✓ KlaraExperiment.horner-function proved
✓ KlaraExperiment.horner-map-sum proved

Ran 9 tests containing 125 assertions.
0 failures, 0 errors.
```

The composition suite still uses its original explicit algebraic/grind proofs;
it was not silently rewritten to depend on the new tactic. Its successful rerun
checks compatibility with this ansatz source/bundle override. The new ring test
independently establishes that this specific Nat polynomial theorem can now be
proved by `(ring)` and used as a kernel-checked equality.

## Trust and scope

The new bundle contains **5,117** declarations, compared with 4,413 in the
earlier experiment. Its manifest records Lean **4.33.1** and the associated
exporter/generation provenance. The port constructs upstream polynomial
normalization certificates, supplying `Eq.refl true` as the Boolean certificate;
the strict checker must reduce the certificate computation and verify its
connection to the original expressions. There is no trusted host-side
polynomial-equality Boolean in the checked proof observed here.

However, the consumer run loaded the bundle in **TRUST mode**. Rechecking the
new theorem application is not independent rechecking of every imported theorem
body. This run did not repeat the ansatz agent's separate bundle-validation
procedure, validate the published artifact, or check CI status. Imported
normalization declarations and their provenance remain part of this run's
trusted base.

The result validates the exact Nat Horner theorem, a nearby false theorem, and
Klara's narrow composition suite. It does not establish all generic semiring/Int
cases, a tactic latency bound, correspondence between mathematical arithmetic
and checked Long execution, interval-analysis soundness, or compiler correctness.
The proof-staging guards and the existing trusted/tested bridges remain necessary.
