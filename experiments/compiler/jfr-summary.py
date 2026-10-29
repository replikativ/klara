#!/usr/bin/env python3
"""Summarize public jfr print output; counts are samples, not exact costs.
Usage: jfr -J-Xmx128m print --events jdk.ExecutionSample,jdk.ObjectAllocationSample \
  --stack-depth 10 /tmp/klara-s17.jfr | python3 experiments/compiler/jfr-summary.py
"""
import collections
import re
import sys

counts, allocations, sites = (collections.Counter() for _ in range(3))
weights = collections.Counter()
for event in sys.stdin.read().split("\n}\n"):
    if "jdk.ExecutionSample {" in event:
        match = re.search(r"stackTrace = \[\n    (.*)", event)
        if match:
            counts[match[1]] += 1
    if "jdk.ObjectAllocationSample {" in event:
        match = re.search(r"objectClass = (.*)", event)
        if match:
            allocations[match[1]] += 1
        stack = event.split("stackTrace = [", 1)[-1]
        match = re.search(r"(clojure.lang.Var.pushThreadBindings[^\n]*|klara\.[^\n]*)", stack)
        weight = re.search(r"weight = ([\d.]+) ([kMGT]?B)", event)
        if match:
            sites[match[1]] += 1
            if weight:
                weights[match[1]] += float(weight[1]) * {
                    "B": 1, "kB": 1024, "MB": 1024**2,
                    "GB": 1024**3, "TB": 1024**4}[weight[2]]
for title, counter in [("Execution sample top frames", counts),
                       ("Allocation sample classes (counts, NOT bytes)", allocations),
                       ("First Klara/Var push allocation frame (sample counts)", sites),
                       ("Sampled allocation weight by first Klara/Var frame (estimated bytes)", weights)]:
    print(title)
    for frame, n in counter.most_common(25):
        print(f"{n:12.0f} {frame}")
