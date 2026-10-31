#!/usr/bin/env python3
"""Run independent JVM campaign cohorts sequentially, preserving raw outputs."""
import argparse
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--processes", type=int, default=3)
    parser.add_argument("--label", default="process")
    args = parser.parse_args()
    if not 1 <= args.processes <= 20 or not args.label.replace("-", "").replace("_", "").isalnum():
        parser.error("use 1..20 processes and an alphanumeric label with optional - or _")
    output = ROOT / "target/compiler-campaign"
    output.mkdir(parents=True, exist_ok=True)
    runs = []
    for i in range(args.processes):
        label = f"{args.label}-{i}"
        command = ["clojure", "-J-Xmx1g", "-J-Xss16m", "-Sdeps",
                   '{:paths ["src" "experiments" "verification" "verification/proof_staging"]}', "-M", "-m", "baseline.campaign", label]
        start = time.perf_counter()
        with (output / f"{label}.log").open("w") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        run = {"label": label, "exit_code": result.returncode,
               "experiment_process_wall_seconds": time.perf_counter() - start, "command": command}
        runs.append(run)
        (output / f"{args.label}-driver.json").write_text(json.dumps(runs, indent=2) + "\n")
        print(json.dumps(run), flush=True)
        if result.returncode:
            raise SystemExit(f"cohort failed; see target/compiler-campaign/{label}.log")


if __name__ == "__main__":
    main()
