# RFC 0004: Canonical EDN encoding for content addressing

- Status: draft
- Owner(s): Christian Weilbach
- Experiments: none yet (CodeIds in S1 use an ad-hoc hash; certificates in S3 hash law and dependency data)
- Obligations: CE1–CE6 below

## Motivation

Klara identifies things by content: CodeIds of canonical expanded syntax,
value-ids of definitions, receipts, certificates, manifests, cache keys of
specializations, and (later) stored worlds and code in datahike/konserve.
All of these are EDN values (architecture: "Data format: EDN"). Two
implementations — the JVM host today, Chez/JS/Wasm later, and the ansatz
spec — must compute **the same hash for the same value**, or certificates
and caches break across hosts and versions. Clojure's `hash` is not suitable:
it is an in-memory hash (32 bits, host-specific numerics, unspecified for
collisions) and it differs across platforms (cljs vs clj).

## Proposal

**1. A canonical byte encoding** `canon : EDN → bytes`, and
`id(v) = SHA-256(version-tag ‖ canon(v))` (truncation allowed only with a
recorded length).

**2. Canonical form rules.**

| EDN | Canonical encoding |
|---|---|
| nil, true, false | fixed one-byte tags |
| integers | one tag for all exact integers (long, BigInt, bigint): minimal two's-complement big-endian magnitude; `1`, `(int 1)`, `1N` encode identically (Klara's `=` semantics, not Java's) |
| ratios | normalized (gcd 1, positive denominator); integer ratios encode as integers |
| floating point | IEEE-754 binary64; `-0.0` and `0.0` distinct; one canonical NaN; floats never equal integers (`(= 1 1.0)` is false in Klara as in Clojure) |
| BigDecimal | unscaled integer + scale, normalized to minimal scale (open: or keep scale — see questions) |
| strings | UTF-8, NFC normalization not applied (bytes as given) — open question |
| keywords, symbols | tag + namespace + name as UTF-8 |
| chars | Unicode scalar value |
| lists, vectors | tag (lists and vectors distinct for identity, though `=`-equal in Clojure — see questions) + count + elements in order |
| maps | tag + count + entries sorted by the canonical bytes of their keys |
| sets | tag + count + elements sorted by their canonical bytes |
| tagged literals | tag symbol + canonical value (`#inst` as integer epoch nanoseconds + offset, `#uuid` as 16 bytes) |
| metadata | **excluded** |
| code values, syntax objects | their α-canonical core term, scope ids replaced by binding structure (de Bruijn) |
| closures, authorities, host objects | **not encodable**: identity requires an explicit, declared projection; encoding fails loudly |

Ordering by canonical bytes (not by a value comparator) makes the order
total, host-independent and cheap to specify.

**3. Versioning.** The encoding carries a version tag; any change to the
rules is a new version, and stored hashes record which version produced them
(the TASTy-style contract from the Scala study).

**4. Equality alignment.** `canon(a) = canon(b)` iff `a` and `b` are Klara-`=`,
with documented exceptions where Klara keeps Clojure's distinctions (the open
questions below). Klara's own collections' `hashCode` (Tier H contract) may be
derived from the same normalization.

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

1. **Numbers.** `hasch.core` encodes numbers via `pr-str`, so `1`, `(int 1)`
   and `1N` may hash differently although they are Klara-`=`. Needs the
   normalization in the table above.
2. **Commutative combination.** hasch combines map entries and set elements by
   **XOR of their hashes** (`benc.cljc`, `xor-hashes`). XOR (like any linear
   combination) admits generalized-birthday collision construction (Wagner
   2002) for adversarially chosen collections. For certificates and receipts,
   which are security-relevant, combine the **sorted child hashes** instead
   (hash of the concatenation of sorted entry hashes). This keeps the merkle
   property — the parent depends only on child hashes, so `HashRef`
   substitution still works — while removing the linear structure.
3. **Metadata exclusion and code values** (α-canonical terms) as in the table.
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
| CE1 | `canon` is a function of the Klara value (independent of host representation: array map vs hash map, Klara map vs Clojure map) | Open |
| CE2 | `canon(a) = canon(b)` ⇔ Klara-`=` except listed exceptions | Open (property test) |
| CE3 | JVM, JS and ansatz-spec implementations agree on a shared test vector corpus | Open |
| CE4 | α-equivalent code values have equal ids; distinct binding structure gives distinct ids | Open |
| CE5 | encoding a closure, authority or host object fails loudly | Open |
| CE6 | existing CodeIds and certificate hashes migrate to `canon` without changing meaning | Open |

## Open questions

1. Lists vs vectors: Clojure's `=` equates `(1 2)` and `[1 2]`. hasch already
   distinguishes them (separate tags); keep that (safer for code, which uses
   lists)?
2. BigDecimal scale: `1.0M` vs `1.00M` are not `=` in Clojure; keep scale?
3. Strings: apply Unicode NFC or hash bytes as given?
4. Wire format: deterministic CBOR via boring (recommended).
5. Fix the gaps in hasch itself (a new versioned mode) or wrap it in Klara?
