# kmap: experiment X2 (Klara core v1 §6, D §4.3 and §6)

This experiment builds a Klara map as a real JVM class, `kmap.core/KMap`, that implements the D §4.3 map interface list. The class wraps a delegate `IPersistentMap`. The delegate is either Clojure's `PersistentHashMap` or `kmap.champ/Champ`, a clean-room CHAMP. The experiment also includes a minimal `defop :single`.

**Clean-room status.** No Clojure Java source was opened, on disk or on the web. Interface signatures were obtained by reflection (`.getDeclaredMethods`, `ancestors`). Every behaviour KMap matches was established by black-box tests (see `results/` and `test/kmap/trap.clj`). Hashes follow clojure.org/reference/data_structures:

- an entry hash is the ordered hash of `[k v]`;
- the map hash is the unordered sum of the entry hashes, passed through the public `mix-collection-hash`.

KMap computes equality and both hashes itself through the delegate's `kvreduce`. It never delegates them, so the tests check the specification, not PHM. The CHAMP was written from the design in Steindorfer & Vinju, OOPSLA 2015:

- two bitmaps per node;
- data stored from the front of the node array and sub-nodes from the back;
- collision nodes once the hash bits are exhausted;
- canonical inlining on delete.

## Layout

| file | content |
|---|---|
| `src/kmap/core.clj` | `KMap`, transient `TKMap`, `kmap`/`wrap`/`deep-kmap`, `*backend*` (:phm / :champ) |
| `src/kmap/champ.clj` | clean-room CHAMP, persistent only, with Clojure key semantics (`hasheq` and `equiv`) |
| `src/kmap/defop.clj` | `defop :single`, `defimpl`, `extend-op!` (~70 lines of code) |
| `test/kmap/gen.clj` | generators: nested maps, vectors, sets and records; long/bigint/double/ratio chosen to collide (1, 1N, 1.0, -0.0, ##Inf); nil, keywords, strings, booleans; numeric retyping for paired maps |
| `test/kmap/core_test.clj` | property tests (10k each) and unit cases |
| `test/kmap/champ_test.clj` | model-based CHAMP vs PHM, 10k op sequences, forced full-hash collisions and hashes that differ only in bits 30–31 |
| `test/kmap/trap.clj` | interface-omission probe (the MapEquivalence / java.util.Map trap) |
| `bench/kmap/bench.clj`, `bench_defop.clj` | Criterium benchmarks |
| `run-all.sh` | reproduces everything in `results/` |

## 1. Property tests: zero failures

Results are in `results/property-tests.txt`. Every property ran 10,000 cases, except the records property (2,000). The whole suite ran against both delegates (PHM and CHAMP).

Each case renders one generated tree three ways: KMap at the top level only, KMap at every nesting level, and a random mix of KMaps and Clojure maps. Each rendering is checked against the plain Clojure map `m`:

- `(= km m)` and `(= m km)`;
- `hash` equality, plus `hash` = `hash-unordered-coll` of the entries;
- membership in `#{m}`, `#{km}`, `{m 1}` and `{km 1}` (array-map and hash-map/hash-set variants);
- `.equals` both ways and `.hashCode` equality;
- `pr-str`, `str` and read-back;
- nesting in both directions (`{:x km}` vs `{:x m}`, `[km]`, `#{km}`, KMap containing Clojure maps), with hashes;
- record fields holding a KMap.

**Relational property.** A second map `m2` is a numeric retyping of the same tree (long↔bigint↔double). It is `=` to `m` about 59% of the time and `.equals` about 39% of the time. For every pair, KMap must give the same answer as PHM for `=` (8 orderings), for `.equals` (3 orderings) and for "`=` implies equal hash". The `.equals`→`.hashCode` contract must hold.

**Ops property.** Each of these is checked against PHM: `count`, `get`/`get` with default/invoke/keyword lookup, `contains?`, `find`, `assoc`, `dissoc`, `conj` (pair, map, entry, nil), `merge` in both directions, `select-keys`, `update-in`, `frequencies`, `distinct`, `group-by`, `into` (from and to KMap), `empty`, `reduce-kv`, `reduce`, `reduced` early exit, `keys`/`vals`, `seq`, `iterator`, transient `assoc!`/`dissoc!`/`persistent!` plus lookups on the transient, map destructuring with `:or`/`:as`, kwargs destructuring, the java.util.Map views (`keySet`/`entrySet`/`containsValue`), copying into `java.util.HashMap` both ways, metadata (outside `=`/hash, preserved by `assoc`/`empty`), `clojure.walk/postwalk`, and `map?`/`coll?`/`record?`/`sequential?`.

**Mutation checks.** Two deliberate bugs were injected and both were caught within 200 cases:

- KMap's `equiv` returning false against an array map;
- an entry hash that leaves out the ordered-collection step.

## 2. Findings: asymmetry and hash mismatches

**F1. The D §4.3 trap is confirmed by black-box test.** Results are in `results/property-tests.txt` (the probe section) and `test/kmap/trap.clj`. Each wrapper uses KMap's own `equiv` rule, with one interface left out at a time. `clj` is the Clojure map, `x` the wrapper.

| omitted | `(= clj x)` | `(= x clj)` | hash= | `(contains? #{clj} x)` | `(contains? #{x} clj)` | `[clj]=[x]` / `[x]=[clj]` | `.equals` clj→x / x→clj |
|---|---|---|---|---|---|---|---|
| nothing | true | true | true | true | true | true / true | true / true |
| `MapEquivalence` | **false** | true | true | true | **false** | **false** / true | true / true |
| `java.util.Map` | **false** | true | true | true | **false** | **false** / true | **false** / true |
| `IHashEq` | true | true | **false** | **false** | **false** | true / true | true / true |

- Leaving out either interface makes `=` asymmetric. The asymmetry spreads into vectors and into set membership, in one direction only.
- Leaving out `IHashEq` keeps `=` symmetric but breaks every hashed container. The fallback `.hashCode` follows the java.util.Map formula, not hasheq.
- With every interface present, no asymmetry or hash mismatch appeared in 30k+ generated cases on either delegate.

**F2. Clojure's own maps break the java.util.Map `equals`/`hashCode` contract.** This comes from Clojure, not KMap, and lies outside the generator's domain. Key lookup in `.equals` uses Clojure equivalence, but `.hashCode` uses Java `hashCode`:

```
(.equals {(int -1) :x} {-1 :x})          => true
(.hashCode {(int -1) :x})                => -1013911913
(.hashCode {-1 :x})                      =>  1013911912
```

The same happens with `Short` and `BigInteger` keys. It does not happen with `BigInt`, because `(.hashCode -1N)` = `(.hashCode -1)`. KMap reproduces PHM exactly here, so the contract violation is shared, not new. Klara has to choose between matching Clojure (as KMap does) and honouring the Java contract.

**F3. `pr-str` equality depends on iteration order.** It is not a value property. A KMap with a PHM delegate and an `=` array map can print in different orders, exactly as array maps and hash maps do in Clojure. A CHAMP-backed KMap prints in a third order. The first property run failed for this reason alone, and the property was restated:

- KMap prints exactly like its delegate;
- `read-string` of the printed form is `=` to `m`;
- KMap prints like PHM when the delegate is PHM.

Klara must not use printed form as identity (content hashes, golden tests) across representations.

**F4. Smaller black-box facts KMap had to match:**

- `toString` is **not** inherited, while `pr-str` works through `print-method`'s `IPersistentMap` dispatch even without a method of its own. A wrapper without `toString` prints `kmap.trap.AllIfaces@3c6f0c28` under `str`.
- `persistent!` drops metadata.
- `empty` keeps metadata.
- A no-op `assoc`/`dissoc` returns the identical map.
- `conj` accepts a `Map$Entry`, a 2-vector (any other vector throws "Vector arg to map conj must be a pair"), nil, or a seqable of entries. A list of vectors throws `ClassCastException`.
- PHM is not `IReduceInit` (by reflection). KMap is, which makes `into {}` from a KMap faster.
- `(hash 0.0)` = `(hash -0.0)` = 0 in 1.12, so `-0.0` caused no mismatch.

## 3. Map benchmarks (Criterium)

**Read these as indicative. The pass/fail verdict at 1.1x is not resolvable on this machine.** The 8-core host was shared with other agents (load average 9–18 during every run). Raw files:

- `results/bench-maps.txt`: interleaved PHM / KMap / CHAMP-KMap, 3 rounds, minimum of `quick-benchmark` means (the primary data).
- `results/bench-maps-isolated.txt`: one implementation per JVM, 2 rounds.

The same operation varied up to 2–3x between the two runs. For example, PHM `=` at n=100k measured 13 ms interleaved and 42 ms isolated. `get`/`assoc` run 8 operations per measurement, and `kw-lookup` uses 8 keyword call sites.

Interleaved ratios to PHM (lower is better):

| op | n=8 KMap | n=8 CHAMP | n=1k KMap | n=1k CHAMP | n=100k KMap | n=100k CHAMP |
|---|---|---|---|---|---|---|
| get ×8 | 1.11 | 1.29 | 1.33 | 1.98 | 1.29 | 2.33 |
| assoc ×8 | 1.10 | 1.11 | 1.24 | 1.35 | 1.06 | 1.10 |
| reduce-kv | 1.13 | 0.90 | 1.01 | **0.35** | 1.06 | **0.62** |
| into {} (from) | 1.07 | 1.01 | 0.82 | 0.81 | 0.79 | 0.80 |
| into (empty m) | 1.08 | 1.37 | 0.94 | 1.48 | 0.83 | 1.70 |
| = (equal copies) | 1.18 | 1.36 | 0.86 | 1.25 | 0.83 | 1.35 |
| hash (cached) | 1.36 | 1.42 | 1.43 | 1.41 | 1.79 | 1.74 |
| assoc+hash (uncached) | 0.92 | 0.88 | **0.52** | **0.44** | 0.72 | 0.60 |
| keyword lookup ×8 | 1.45 | 2.08 | 1.21 | 2.02 | 1.08 | 2.28 |
| postwalk 11,111 nodes | 1.00 | 1.54 | | | | |

What the numbers say, beyond the noise:

- **The delegate wrapper costs one interface hop per lookup:** about 2–7 ns per `get` or keyword lookup, and one 32-byte allocation per `assoc`. Against PHM's 15–25 ns lookups on this loaded host, that is 1.1–1.45x on lookup-bound microbenchmarks. Cached `hash` is 7–12 ns absolute either way. **The delegate does not meet ≤1.1x on get, keyword lookup or cached hash.** Closing that gap needs a native representation (CHAMP done well, or emitted classes), not a wrapper.
- **KMap's own equality and hash beat PHM's:** `=` up to 0.83x, uncached hash 0.5–0.7x, and `into {}` from KMap 0.8x. KMap's `kvreduce` path allocates no entries. The cost model is now clear: equality and hashing written against `kvreduce`, not against entry iteration, are already faster than what Clojure does.
- **CHAMP (optional step, done):**
  - iteration is 1.6–2.9x faster than PHM (`reduce-kv`), as the paper predicts;
  - lookups are about 2x slower. This untuned Clojure-written version goes through `definterface` dispatch, int/long conversions and per-level `Util/equiv`;
  - `into (empty m)` and `postwalk` are 1.5–1.7x slower because the CHAMP has no transients (KMap falls back to a persistent-behind-transient facade).
  - **CHAMP misses ≤1.3x on get, keyword lookup, into/postwalk and `=`.** The fixes are known: specialize node classes by arity, add an `IEditableCollection` with owner tokens, and cache key hashes in collision nodes.

## 4. defop :single vs protocol (O6)

`defop` stores one immutable cache snapshot in a volatile field:

- 2 inline-cache slots compared by class identity;
- then an open-addressed `identityHashCode` class→fn table;
- then a miss that resolves through the superclass chain, then interfaces, then `Object`. An ambiguous interface match is an error.

`extend-op!` replaces the method map and resets the cache (a new version). The cache is per op, not per call site. A true per-site inline cache, or a `MutableCallSite`, needs `invokedynamic` emission, which plain Clojure cannot do cleanly.

In the benchmark, each (implementation, scenario) pair runs in its own JVM, and the whole set ran twice (`results/bench-defop.txt`). Each measurement is a loop over 1,024 receivers. The protocol is extended to the types with `extend-protocol`, not implemented inline.

| site | protocol ns/call (run1 / run2) | defop ns/call | defop/protocol |
|---|---|---|---|
| mono (KMap) | 4.25 / 3.91 | 3.42 / 2.71 | 0.81 / 0.69 |
| poly-2 (KMap, PHM) | 11.34 / 8.10 | 7.31 / 4.36 | 0.64 / 0.54 |
| poly-3 (+ PAM) | 14.54 / 10.91 | 14.08 / 8.82 | 0.97 / 0.81 |
| mega (8 types) | 34.43 / 20.27 | 24.93 / 14.82 | 0.72 / 0.73 |

**This passes with margin:** defop is 0.54–0.97x of the protocol (target ≤1.2x). The largest gain is at the 2-type site, where the two inline-cache slots avoid the protocol's cache lookup. This comparison is not against inline `deftype` protocol implementations, which compile to a direct interface call.

## 5. Verdict against the pass targets

| target | result |
|---|---|
| zero property failures | **pass**: 30k cases on each of two delegates, plus 10k CHAMP model cases; the interface-omission probe shows the tests can detect the trap |
| delegate ≤1.1x PHM on every op | **fail on lookups**: get 1.1–1.3x, keyword lookup 1.1–1.45x, cached hash about +8 ns; **pass or better** on `=`, uncached hash, `into`, `reduce-kv`, `postwalk` and `assoc` at n=100k. Measured under heavy shared load, so ±20% noise. |
| CHAMP ≤1.3x PHM | **fail** on get/keyword lookup (about 2x), into-same/postwalk (1.5–1.7x) and `=` (1.25–1.36x); **wins** on `reduce-kv`/hash |
| defop ≤1.2x protocol | **pass**: 0.54–0.97x |

## Conclusions for the design

1. The D §4.3 order is right and sufficient. `IPersistentMap` + `MapEquivalence` + `java.util.Map` + `IHashEq` gives symmetric `=` and hash parity across all generated mixtures of numerics, records and nesting, with hashes computed from the public spec only. Each of the three non-obvious interfaces fails in its own way when left out (table F1). Add that table to D as the falsifier for O5.
2. Parity means matching Clojure's quirks, including breaking the Java Map contract for `Integer`/`Short`/`BigInteger` keys (F2). Decide that explicitly.
3. Never treat printed form as a value identity across representations (F3).
4. Wrapping costs about 5 ns per lookup. Phase 1 should emit native classes, or a tuned CHAMP with transients, rather than wrap.
5. `defop :single` with a 2-slot cache plus a class table already beats extended protocols from plain Clojure. O6 looks safe; per-site caches via an emitter are an optimisation, not a requirement.

Re-run with `./run-all.sh`, preferably on a quiet machine: the benchmark verdicts at 1.1x need one.
