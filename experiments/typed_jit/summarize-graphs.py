"""Summarize the first Final HIR schedule in each Graal text CFG dump."""
import collections
import json
import pathlib
import re
import sys

rows = []
for path in sorted(pathlib.Path(sys.argv[1]).glob("*.cfg")):
    text = path.read_text().split("end_cfg", 1)[0]
    if 'name "Final HIR schedule"' not in text:
        continue
    nodes = collections.Counter(re.findall(r"instruction <@([^|]+)\|@", text))
    rows.append({
        "file": path.name,
        "nodes": sum(nodes.values()),
        "blocks": text.count("begin_block"),
        "node_kinds": dict(sorted(nodes.items())),
        "call_targets": sorted(set(re.findall(r"^targetMethod: (.*)$", text, re.M))),
    })
print(json.dumps(rows, indent=2))
