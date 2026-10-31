"""Summarize JFR samples whose captured stacks include the Klara evaluator.

Input: jfr print --json --events jdk.ObjectAllocationSample RECORDING
Weights are sampling estimates, not exact allocation counts. Stack depth and
inlining limit attribution; recordings include preparation and startup.
"""
import collections
import json
import sys

with open(sys.argv[1]) as source:
    events = json.load(source)["recording"]["events"]
classes = collections.Counter()
sites = collections.Counter()
hits = 0
for event in events:
    value = event["values"]
    frames = (value.get("stackTrace") or {}).get("frames", [])
    methods = [frame["method"]["type"]["name"].replace("/", ".") + "." + frame["method"]["name"]
               for frame in frames]
    evaluator = [method for method in methods if method.startswith("klara.eval$")]
    if evaluator:
        hits += 1
        classes[value["objectClass"]["name"]] += value["weight"]
        sites[evaluator[0]] += value["weight"]
print(json.dumps({"scope": "samples with a captured klara.eval frame; includes startup/preparation; limited stack depth",
                  "sample_events": len(events), "eval_sample_events": hits,
                  "sample_weight_bytes": sum(classes.values()),
                  "classes": classes.most_common(), "sites": sites.most_common()}, indent=2))
