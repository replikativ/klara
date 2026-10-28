# RFC 0007: Modules, signatures and abstract identity

- Status: draft
- Owner(s): Christian Weilbach
- Builds on: research note P (ML family), RFC 0006 (languages), RFC 0004 (canonical EDN)
- Obligations: MD1–MD5 below

## Motivation

Worlds select definition versions; `defop` provides dispatch; language
descriptors select semantics. None of them provides **representation
independence** or **sharing**: the guarantee that clients of an abstraction
cannot depend on its representation, and that two components agree they use
the same abstract type. ML modules solve this with signatures, opaque sealing
and generative functors. Research note P corrects an assumption made earlier:
**content hashes do not give generativity** — applying the same constructor
twice to the same data may intentionally create incompatible abstract types,
which no hash of code and data can encode.

## Proposal

1. **Signatures are immutable contract data** (EDN in the world): exported
   names, shapes, **abstract identity tokens**, effect and authority
   obligations, optional laws with evidence status.
2. **Export bundles** are maps from names to values, referencing a signature.
   A **module constructor** (functor) is an ordinary function from dependency
   bundles to an export bundle.
3. **Generative seals.** Sealing a bundle against a signature mints fresh
   abstract identity tokens (an authority-like operation: minting is
   recorded and scoped). Values of a sealed abstract type carry the token;
   clients see only the signature's operations.
4. **Explicit sharing.** A signature may state that an abstract type equals one
   from another bundle (sharing constraint); checked when bundles are
   combined. Applicative (non-generative) identity is a later opt-in.
5. **Checking by language.** An ML-like typed descriptor (RFC 0006) checks
   module constructors statically; dynamic clients receive wrappers and seals
   (contracts with blame).
6. **Identity and versioning.** A module instance records its construction
   recipe (constructor CodeId, argument identities) and the fresh seals it
   minted. Code identity excludes accidental allocation identity. Restoring a
   persisted instance preserves its seals as stable identities (rules to be
   specified before serializing seals).
7. **Specialization.** Known module arguments permit specializing a
   constructor's body under recorded dependency assumptions (the MLton
   analogy), without running initialization effects early.
8. **Not a language descriptor.** One descriptor per ordinary module would
   conflate language choice with packaging; modules and languages stay
   distinct.

## Acceptance example

Real World OCaml's `Foldable.Extend`: derive operations from a foldable
module while preserving its abstract type, and two generative abstract stores
whose values must not be accepted across each other through checked APIs.

## Obligations

| Id | Obligation | Status |
|---|---|---|
| MD1 | Values of distinct generative seals are never accepted across checked APIs | Open |
| MD2 | Declared sharing is checked when bundles combine | Open |
| MD3 | Specializing a constructor preserves initialization-effect order | Open |
| MD4 | Restored instances keep their seal identities; consumed authorities are not resurrected | Open |
| MD5 | Erasing static module checks leaves dynamic seals sufficient for representation independence | Open |

## Open questions

1. First client that justifies typed modules: inference kernels, reusable
   collection libraries, or the proof checker?
2. Who may mint seals, and do seals survive restoration as stable identities?
3. Shared versioning with language descriptors (RFC 0006)?
