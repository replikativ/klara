"""Summarize TSV samples as ranges of process medians, microseconds."""
import collections
import csv
import pathlib
import statistics
import sys

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "target/chez-empirical")
groups = collections.defaultdict(list)
for path in sorted(root.glob("*.tsv")):
    if path.name in {"semantics.tsv", "summary.tsv", "startup.tsv"}:
        continue
    for row in csv.reader(path.open(), delimiter="\t"):
        process, mode, workload, phase, sample, ns, value = row
        kind = "runtime" if path.name.startswith("runtime-") else "scale" if path.name.startswith("scale-") else "aot"
        groups[kind, mode, workload, phase, process].append(float(ns) / 1000)
cohort = collections.defaultdict(list)
for (*key, process), values in groups.items():
    cohort[tuple(key)].append(statistics.median(values))
print("kind\tmode\tworkload\tphase\tprocesses\tmin-us\tmax-us")
for key, values in sorted(cohort.items()):
    assert len(values) == 3, (key, values)
    print(*key, len(values), f"{min(values):.3f}", f"{max(values):.3f}", sep="\t")
