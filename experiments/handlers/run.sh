#!/usr/bin/env bash
# Usage: ./run.sh <java-binary> <out-file> <rounds> [bench-ids...]
# One JVM per benchmark, rounds interleaved, pinned to P-cores 1-3.
set -euo pipefail
cd "$(dirname "$0")"
JAVA=${1:-java}; OUT=${2:-results/raw.edn}; ROUNDS=${3:-3}; shift 3 || true
CP=$(cat results/classpath.txt)
IDS=("$@")
if [ ${#IDS[@]} -eq 0 ]; then
  IDS=($("$JAVA" --add-exports java.base/jdk.internal.vm=ALL-UNNAMED -cp "$CP" clojure.main -e "(require 'klara.bench) (doseq [k (sort (keys klara.bench/benches))] (println (subs (str k) 1)))"))
fi
for r in $(seq 1 "$ROUNDS"); do
  for id in "${IDS[@]}"; do
    line=$(taskset -c 1-3 "$JAVA" --add-exports java.base/jdk.internal.vm=ALL-UNNAMED \
      -Xms1g -Xmx1g -XX:+UseParallelGC -cp "$CP" clojure.main -m klara.bench "$id" 2>&1 | tail -1)
    echo "{:round $r :load \"$(cut -d' ' -f1 /proc/loadavg)\" :run $line}" >> "$OUT"
    echo "round $r $id done"
  done
done
