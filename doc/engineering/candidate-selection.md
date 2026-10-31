# Candidate selection and source-bound evidence

Implemented 2026-10-30. This follows [funded strategies](preparation-strategies.md)
and the [enclosed private endpoint](private-accumulator.md). Publication accepts
only validated candidates; selection chooses among candidates whose world,
argument, capture and handler premises hold. Priority is a preference, not
evidence of correctness or measured profitability.

## Named variants and ordering

An explicitly funded guest request can attach selection metadata:

```clojure
(perform :stage/prepare-request subject
  {:job job
   :strategy 'klara.private-optimizer/policy
   :selection {:variant :private :priority 10}})
```

The result still needs normal validation and installation after leaving its
preparation fork. Startup preparation jobs accept the same `:selection` option.
This does not register a strategy to run on each function call.

An explicit variant name is a replacement slot within one original source
CodeId. Two different variant names coexist even when their guards are equal.
Reinstalling the same name replaces that slot, including its guards and
priority. The identifier must be a bounded keyword, and priority a signed
64-bit integer. Extra keys and malformed descriptors reject before publication.

Candidates are ordered by descending priority, then lexicographic variant
name. At equal priority, explicit variants precede legacy slots. Legacy
candidates retain assumption-set replacement slots with priority zero;
overlapping legacy slots use first-installation order, preserved on replacement.
Explicit names therefore give installation-order-independent ties; legacy
behavior is deterministic for a given publication history. Priority may be
negative. It does not bypass a failed guard or a stale world dependency.

Ordering is computed on atomic publication and invalidation, not sorted on
every call. Ordinary entry, compiler direct-entry sites and immutable-evidence
sites use the ordered candidates. Each interface still imposes its eligibility
conditions: for example, an evidence site requires an admitted unary worker.
Publication changes the cache snapshot and refreshes cached site decisions.
Deleting the cache still leaves T0 as fallback.

The [entry-plan follow-up](candidate-selection.md#live-entry-plans) corrects direct slots to retain ordered
candidates rather than one cached winner or miss. Live host-root checks can make
a preferred candidate valid again without a new Klara root or publication. Each
call must reconsider it, or choose the next candidate if the former winner
fails. Opaque/layout-sensitive candidate groups still use ordinary entry.

`klara.selection-test` covers overlapping guards, equal-guard coexistence,
stable ties, priority replacement, rejected descriptors, direct/evidence-site
refresh, old pinned worlds and sweeping invalid candidates. It makes no
claim that the highest-priority candidate is the fastest. There is no automatic
promotion/retirement or measured-profitability policy in this change.

## One source relation admission check

The baseline checker now delegates the structural relation to
`klara.compile.relation/check`. For both unchanged emission and rewrite chains,
the named origin must reconstruct well-scoped indexed Core with the original
entry's CodeId. A matching chain of endpoint hashes alone is insufficient.
The check then requires opaque connected edges, one contract, bounded chain
length and receipts equal to their accepted edge descriptions. Endpoint-specific
ownership and runtime-premise checks remain mandatory.

Prepared information exposes the source/residual identities, recipe rules and
the hosted-evidence status. It does not label the chain kernel-proved. The
baseline candidate retains its original entry identity through local inlining
and the final owned representation change. The tests reject an origin attached
to a different original function, missing/malformed origins, changed receipts
and an unrelated residual on the unchanged path.

This shared check is structural admission for the current baseline adapters.
It is not a universal proof protocol for arbitrary Code, and it does not
silently upgrade the separate scalar, fusion or other experimental backends.
Trusted hosted code remains responsible for registering checkers and issuing
accepted recipe capabilities.

The [actual inline correspondence follow-up](actual-inline-correspondence.md)
adds an independent indexed elimination check before issuing a local-call edge
and rechecks it at source-relation admission. This detects malformed lexical
bindings, incorrect argument lifting and wrong residuals. The hosted decoder
and full evaluator/backend correspondence remain tested bridges.

## Validation receipts and late backend loading

A prevalidation receipt binds the exact executable and checker-registry
snapshot. Loading an optional backend can register a checker, making an earlier
receipt stale for later publication. Revalidate the candidate before publishing
it under that new registry; do not bypass the registry identity check. Already
installed candidates retain their own runtime premises. Registry changes are
not an automatic retirement policy for installed code.

The wider campaign's fresh-process run caught this when assembling a portfolio
from previously prepared candidates. Its harness renews stale receipts and
includes that work in portfolio publication cost. A warm REPL with all backends
loaded would not expose this initialization order.

## Live entry plans

### What can be retained

Publication splits world and runtime guards as before and derives an immutable
runtime plan. For an already loaded, qualified host symbol, that plan records
the namespace, its immutable mapping generation and the Var found in that exact
mapping. A weak reference to the mapping avoids retaining superseded namespace
maps. Publication does not require or load an unresolved namespace.

At each host-root guard, the plan checks that the namespace is still registered,
the caller's alias does not redirect the prefix, and the mapping generation is
unchanged. It then dereferences the Var and compares the **current value** with
the expected root. Dereference preserves thread-local dynamic bindings. A changed
mapping, removed namespace, alias redirection or cleared weak reference uses the
ordinary resolver instead. It can therefore accept a replacement Var with the
same value, reject a changed value, or raise the same resolution failure when
that guard is reached.

This retains an address-resolution plan, not a host-root verdict. The actual
guard vector and candidate vector are traversed in order using indexed persistent
vectors. Argument predicates run as before; their results are not memoized across
candidates or invocations. World validity retains the existing per-executable,
immutable-root memo. The ordinary context and continuation construction remain.

For example, this ordering must survive optimization:

```clojure
;; Candidate A, followed by candidate B:
[[:host-root 'example/helper expected-helper]
 [:arg 0 :application-predicate]]
[[:host-root 'example/helper expected-helper]]
```

The predicate may change `example/helper` before returning false. B must read it
again. An unresolved host name must not be loaded before an earlier argument
guard has passed. These cases prevent general invocation-local verdict sharing.

Plans are used only with the canonical guard evaluator; overriding that evaluator
before publication or entry falls back to ordinary evaluation. Arbitrary changes
to trusted Clojure resolver implementations are outside this contract. Host-root
checks also do not provide an atomic snapshot of concurrent host mutation or a
sandbox for arbitrary host effects. Klara world validity and host-memory validity
remain separate obligations.

### Identity-cache collisions

The bounded entry CodeId cache now uses 512 atomic slots with four immutable
entries per slot, retaining at most 2,048 terms. Keys include term identity and
the current CodeId implementation identity; Clojure equality would conflate some
numeric representations. Atomic publication prevents torn or lost slot updates.
Eviction only causes recomputation, never reuse for a different term/version.

The former direct-mapped slot allowed a caller and its nested loop closure to
evict each other on every interpreted call. A forced same-source collision probe
reproduces roughly 1 ms and 4 MB per call in the old cache control. Four ways
retain both terms and remove that repeated hashing in the probe. This is a
bounded cache improvement, not a guarantee of no capacity misses: more than four
active terms sharing a slot can still thrash, and cold canonical hashing remains
expensive. The separate Core CodeId cache is unchanged.

### Direct and evidence sites

The direct-site cache now retains the ordered candidate list and pure shape
facts under the same root, source term, publication generation and arity. Each
call selects the first currently eligible candidate, checking live host roots in
runtime guard order. Previously a cached lower-priority winner, or a cached miss,
could hide a preferred candidate after its host root became valid again. A
winner becoming invalid must also allow the next eligible candidate.

Only the closed fixed-arity compiler interface can retain these shape facts:
empty canonical captures/statics, bounded arity and canonical keyword handler
sets, under admitted handler context. Layout-sensitive, opaque or mixed candidate
groups use ordinary entry with actual arguments. World validity remains checked
in candidate order. Direct-site hit/fallback counters retain their slot-fill
meaning; they are not counts of every native invocation.

Evidence sites use the same host-binding plans but retain their separate
subject-bound argument evidence rules. This change creates no new argument
facts and extends no evidence lifetime. The diagnostic `stage/*entry-mode*`
`:reference` selects the original ordinary-entry guard traversal; it is not an
old-release control for the corrected direct-site algorithm.

### Evidence and remaining work

[`klara.entry-test`](../../test/klara/entry_test.clj) covers live/dynamic roots,
namespace replacement and aliases, deferred resolution, weak-reference misses,
mutating predicates, guard-evaluator overrides, direct priority recovery,
cached-miss recovery, handler admission, resolution-failure order and colliding
CodeId entries with implementation changes. Existing
selection and staging suites cover publication changes and pinned worlds.
These are regression tests, not a new kernel proof of runtime dispatch.
