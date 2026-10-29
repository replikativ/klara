# Independent validation of the merged ring implementation

The unchanged [ring validation runner](ring_validation.clj) and proof-staging
suite passed against the exact merged ansatz commit
`2191c02737cb194d677ff766b4d87948b5c4fb75` on 28 October 2026:
**10 tests, 135 assertions, zero failures/errors; process exit 0**.

This report is separate from the [earlier isolated-revision validation](ring-validation.md).
No earlier findings, test code, dependency pins, or sibling files were changed.

## Exact inputs and command

`git -C ../ansatz rev-parse HEAD` returned
`2191c02737cb194d677ff766b4d87948b5c4fb75`.
`git -C ../ansatz status --short` returned no entries: the checkout was clean.
Its commit title was `Port ring identities to Lean checked polynomial reflection (#272)`.
The existing `../ansatz/classes` directory supplied compiled Java kernel classes;
this validation did not rebuild Java classes or test a published JAR.

One fresh JVM ran both suites, from the Klara repository root:

```sh
clojure -Sdeps '{:aliases {:ring-validation-final {:extra-paths ["experiments/proof_staging"] :override-deps {org.replikativ/ansatz {:local/root "../ansatz"}}}}}' -J-Xmx3g -J-Xss16m -J--enable-native-access=ALL-UNNAMED -M:ring-validation-final -m ring-validation
```

Fingerprints taken before execution:

| Input in `../ansatz` | SHA-256 |
|---|---|
| `src/ansatz/tactic/ring.clj` | `6af247442564cf29bdf4b9616691610632ce3486fe51f20be01544c43f3ed830` |
| `resources/ansatz/init-medium.ndjson.gz` | `8ec11981455e9c8a046731fc84af424151a02014e788a26ec085cf01617da8e7` |
| `resources/ansatz/bundle.edn` | `accafe7b357688616838ee427e52a5a04a6c8748aa5bb79e36aa32aa4cc2aa68` |
| `classes/ansatz/kernel/TypeChecker.class` | `3df16726bdfca973861b0e4f53787b9da53ad3ebc73e314f3900351820bc9677` |

The manifest records Lean 4.33.1 provenance. The runtime loaded **5,118** bundled
declarations, one more than in the earlier isolated revision. The merged commit
also changes surface arithmetic elaboration; this run validates compatibility
with the exact merged contents rather than assuming the earlier result carries
over. It does not independently exercise all generic arithmetic cases.

## Checks and observed output

The runner loads the unmodified original `ring_probe.clj`, proving

```
∀ a b c x : Nat,
  a + (x*b + (x*x)*c) = a + x*(b + x*c)
```

using `(ring)`. It extracts the resulting closed proof and calls
`ansatz.kernel.env/verifies?` independently. This uses strict kernel checking,
not tactic completion alone or lenient type inference. The proof references
`Lean.Grind.CommRing.eq_normS` and does not cite itself.

The strict check accepts the proof at its original goal and rejects it when the
right-hand side is increased by one. Separately, `(ring)` rejects that false
symbolic identity with a tactic error; the immutable environment remains
unchanged and no false theorem declaration is installed.

```text
Ansatz: loaded the bundled medium Init tier (5118 declarations, TRUST mode).
✓ KlaraExperiment.ring-probe proved
:ring-proof {:declarations 5119,
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

The original composition suite retains its explicit algebraic/grind proofs. Its
rerun covers exact endpoint binding, composition, arithmetic and input guards,
fallback, and handler/host-root refusal under the merged dependency override.

## Evidence boundary

The bundle was loaded in **TRUST mode**. Independently checking the new proof
application does not independently replay every imported theorem body. This run
did not repeat ansatz's bundle-validation procedure, audit CI, or establish a
general theorem about the tactic implementation.

The result validates the exact Nat polynomial proof and the narrow Klara
composition suite at the merged commit. It does not change the established
boundaries: the interpretation of staged code, executable interval analysis,
checked-Long correspondence, authority behavior and backend correctness retain
their existing trusted/tested status. Klara's checked-in dependency pin remains
unchanged; the newer ansatz was selected only by the command-line override.
