"""Wall time includes subprocess creation, Chez startup and minimal script load."""
import os
import pathlib
import subprocess
import sys
import tempfile
import time

out = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "target/chez-empirical")
with tempfile.TemporaryDirectory(prefix="klara-chez-startup-") as directory:
    script = pathlib.Path(directory) / "noop.ss"
    script.write_text("(import (chezscheme))\n")
    with (out / "startup.tsv").open("w") as stream:
        for sample in range(9):
            start = time.perf_counter_ns()
            subprocess.run([os.environ["SCHEME"], "--script", str(script)], check=True,
                           stdout=subprocess.DEVNULL)
            stream.write(f"{sample}\t{time.perf_counter_ns() - start}\n")
