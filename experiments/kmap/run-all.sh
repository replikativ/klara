#!/usr/bin/env bash
# Runs property tests (both backends), map benchmarks, defop benchmarks.
set -u
cd "$(dirname "$0")"
mkdir -p results
clojure -M:test -m kmap.run-all > results/property-tests.txt 2>&1
echo "tests exit $?" >> results/property-tests.txt
clojure -M:bench -m kmap.bench > results/bench-maps.txt 2>&1
rm -f results/bench-defop.edn
: > results/bench-defop.txt
for round in 1 2; do
  for sc in mono poly2 poly3 mega; do
    for impl in protocol defop; do
      clojure -M:bench -m kmap.bench-defop $impl $sc results/bench-defop.edn >> results/bench-defop.txt 2>&1
    done
  done
done
echo DONE >> results/bench-defop.txt
rm -f results/bench-maps-isolated.edn
for i in phm kmap champ; do clojure -M:bench -m kmap.bench isolated $i; done > results/bench-maps-isolated.txt 2>&1
