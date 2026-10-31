#!/bin/sh
# Run from repository root; SCHEME and SCHEMEHEAPDIRS select the isolated build.
set -eu
: "${SCHEME:?set SCHEME to native Chez executable}"
OUT=${1:-target/chez-empirical}
mkdir -p "$OUT"
"$SCHEME" --script experiments/interpreter/chez/semantics.ss > "$OUT/semantics.tsv"
for process in 0 1 2; do
  if [ "$process" = 1 ]; then modes='no-cp0 default'; else modes='default no-cp0'; fi
  for mode in $modes; do
    "$SCHEME" --script experiments/interpreter/chez/measure.ss runtime "$mode" "$process" "$OUT" > "$OUT/runtime-$mode-$process.tsv"
    "$SCHEME" --script experiments/interpreter/chez/measure.ss aot-build "$mode" "$process" "$OUT" > "$OUT/aot-build-$mode-$process.tsv"
    for workload in sum calls copy-vector ledger; do
      "$SCHEME" --script experiments/interpreter/chez/measure.ss aot-run "$mode" "$process" "$OUT" "$workload" > "$OUT/aot-run-$mode-$workload-$process.tsv"
    done
  done
done
for process in 0 1 2; do
  for mode in default no-cp0; do
    "$SCHEME" --script experiments/interpreter/chez/scale.ss "$mode" "$process" > "$OUT/scale-$mode-$process.tsv"
  done
done
python3 experiments/interpreter/chez/startup.py "$OUT"
python3 experiments/interpreter/chez/summarize.py "$OUT" > "$OUT/summary.tsv"
