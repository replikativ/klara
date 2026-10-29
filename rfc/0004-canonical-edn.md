# RFC 0004: Canonical EDN encoding for content addressing

- Status: draft
- Owner(s): Christian Weilbach
- Experiments: S30 implements representation-sensitive Core canonical format v1 and identity-keyed memoization; a portable common EDN/graph codec remains proposed
- Obligations: CE1–CE6 below

## Motivation

Klara uses content identities for canonical expanded syntax, receipts,
certificates, manifests, specialization keys and (later) stored worlds and
code in datahike/konserve. Definition `value-id`s instead identify fresh
evaluation generations: identical source can evaluate to different data, so
they are not content hashes (S32). The content-addressed objects are EDN values
(architecture: "Data format: EDN"). Two
implementations — the JVM host today, Chez/JS/Wasm later, and the ansatz
spec — must compute **the same hash for the same value**, or certificates
and caches break across hosts and versions. Clojure's `hash` is not suitable:
it is an in-memory hash (32 bits, host-specific numerics, unspecified for
collisions) and it differs across platforms (cljs vs clj).

## Identity profiles (clarification after S30)

Clojure `=` is too coarse for executable or resumable-state identity. Equal
Long and BigInt literals can have different overflow behavior; S30 reproduced
and fixed an actual wrong-cache-hit counterexample. The current Core v1 format
preserves quoted numeric classes and uses bounded term-identity memoization.
It is an implementation format, not the completed portable codec below.

Distinguish a declared mathematical/logical value quotient from executable Core
identity and a lossless deployment-state encoding. Each profile states its
observations, representation rules, metadata treatment and version. Reusing
one normalized numeric hash for all three is unsound. Source/format provenance
may also need a separate identity from alpha-canonical executable meaning.
General metadata, opaque-host values and identity-observing contexts remain
outside the current CodeId adequacy claim.

## Proposal

**1. Profile-indexed canonical byte encoding** `canon_profile : SupportedEDN → bytes`, and
`id(v) = SHA-256(profile-tag ‖ version-tag ‖ canon_profile(v))` (truncation allowed only with a
recorded length).

**2. Canonical form rules.**

| EDN | Canonical encoding |
|---|---|
| nil, true, false | fixed one-byte tags |
| integers | runtime/code profiles preserve numeric representation (e.g. Int32, Long64, arbitrary integer) plus exact magnitude; a separately declared mathematical quotient may normalize them |
| ratios | exact numerator/denominator; cross-representation normalization only in a declared logical quotient |
| floating point | preserve Float32/Float64 and the chosen observable bit/value distinctions; signed-zero and NaN policy must be explicit per profile |
| BigDecimal | unscaled integer + scale for a lossless runtime profile; normalization only under an explicit quotient |
| strings | UTF-8, NFC normalization not applied (bytes as given) — open question |
| keywords, symbols | tag + namespace + name as UTF-8 |
| chars | Unicode scalar value |
| lists, vectors | tag (lists and vectors distinct for identity, though `=`-equal in Clojure — see questions) + count + elements in order |
| maps | tag + count + entries sorted by the canonical bytes of their keys |
| sets | tag + count + elements sorted by their canonical bytes |
| tagged literals | tag symbol + canonical value (`#inst` as integer epoch nanoseconds + offset, `#uuid` as 16 bytes) |
| metadata | profile-specific; lossless state/source encoding retains observable metadata, while current Core v1 excludes it with adequacy explicitly restricted |
| code values, syntax objects | their α-canonical core term, scope ids replaced by binding structure (de Bruijn) |
| closures, authorities, host objects | **not encodable**: identity requires an explicit, declared projection; encoding fails loudly |

Ordering by canonical bytes (not by a value comparator) makes the order
total, host-independent and cheap to specify.

**3. Versioning.** The encoding carries a version tag; any change to the
rules is a new version, and stored hashes record which version produced them
(the TASTy-style contract from the Scala study).

**4. Observation alignment.** The selected profile must distinguish values
whose declared observations differ. Deterministic encoding is separate from
semantic adequacy; hash uniqueness additionally assumes collision resistance.
An explicitly chosen mathematical quotient may align with a logical equality,
but Clojure `=` is not the universal equivalence for code or state. Collection
lookup hashing may follow equality rules different from executable identity.

## Building on hasch and boring (added 2026-10-28)

Klara should build on replikativ's existing libraries rather than invent a
new encoding:

- **hasch** (`../hasch`, Christian's library; EPL-1.0 with a few outside
  contributors, so Klara depends on it as a separate module unless it is
  relicensed) already gives cross-platform (JVM/JS) deterministic hashing of
  EDN, distinct tags for seqs and vectors, and **structural (merkle) hashing**
  in `hasch.core`: replacing any subtree by its `HashRef` leaves the parent
  hash unchanged. That property is valuable for Klara (incremental hashing of
  worlds, code and receipts; hashing a stored value without loading it) and is
  kept.
- **boring** (deterministic CBOR, RFC 8949) is the natural wire format.

Gaps between hasch and this RFC, to resolve in hasch (or a versioned hasch
mode) rather than in Klara:

1. **Numbers.** Select and version an identity profile. `pr-str` alone does
   not preserve every runtime numeric class, and blindly normalizing equal
   numbers loses behavior needed for code/state identity. Mathematical-value
   normalization, if desired, is a separate profile.
2. **Commutative combination.** hasch combines map entries and set elements by
   **XOR of their hashes** (`benc.cljc`, `xor-hashes`). XOR (like any linear
   combination) admits generalized-birthday collision construction (Wagner
   2002) for adversarially chosen collections. For certificates and receipts,
   which are security-relevant, combine the **sorted child hashes** instead
   (hash of the concatenation of sorted entry hashes). This keeps the merkle
   property — the parent depends only on child hashes, so `HashRef`
   substitution still works — while removing the linear structure.
3. **Metadata treatment and code values** (alpha-canonical terms) according
   to the selected profile and its stated adequacy scope.
4. **Versioning tag** in every hash.

## Alternatives considered

- **Clojure `hash`**: in-memory, 32-bit, platform-specific; not for storage.
- **Deterministic CBOR (RFC 8949 §4.2)**: close to this proposal and a good
  wire format; lacks keywords, symbols, sets and tagged-literal semantics
  natively (they would need CBOR tags). Option: define `canon` as
  deterministic CBOR with registered tags for EDN-specific types.
- **Fressian**: rich, but not canonical (caching, ordering) without extra
  rules.
- **Unison's hashing** (studies/unison.md): the model for code hashing
  (names erased, mutually recursive components hashed together); adopted for
  code values.

## Obligations and falsifiers

| Id | Obligation | Status |
|---|---|---|
| CE1 | Each profile is deterministic and independent of representation differences declared unobservable by that profile | Open |
| CE2 | Each profile preserves its declared observable distinctions; executable identity separates Long/BigInt behavior | S30 numeric regression tested; general adequacy open |
| CE3 | JVM, JS and ansatz-spec implementations agree on a shared test vector corpus | Open |
| CE4 | Alpha-equivalent admitted Core has equal canonical encodings; required binding/representation distinctions are preserved | Tested subset; general adequacy and portable profile open |
| CE5 | encoding a closure, authority or host object fails loudly | Open |
| CE6 | Version/profile changes explicitly rebuild or validate artifacts, without silently reusing incompatible ids | S30 requires rebuilding v0 ids; general migration protocol open |

## Open questions

1. Lists vs vectors: Clojure's `=` equates `(1 2)` and `[1 2]`. hasch already
   distinguishes them (separate tags); keep that (safer for code, which uses
   lists)?
2. Which runtime observations does each numeric/metadata profile preserve?
   Lossless storage must retain representation distinctions even when equality
   ignores them.
3. Strings: apply Unicode NFC or hash bytes as given?
4. Wire format: deterministic CBOR via boring (recommended).
5. Fix the gaps in hasch itself (a new versioned mode) or wrap it in Klara?
