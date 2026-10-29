#!/usr/bin/env python3
"""Build a public, frozen development artifact from intended source paths.

Private working material is excluded. Working-tree edits are included and
identified by file hashes; external dependencies are not vendored.
"""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
TOP = {"README.md", "STATUS.md", "CONTRIBUTING.md", "LICENSE", "deps.edn", ".gitignore"}
DIRECTORIES = {"src", "test", "test-integration", "test-spec", "spec", "examples", "rfc", "doc", "scripts", "notebooks"}
EXPERIMENTS = {"consolidation", "proof_staging", "adaptive_affine", "pldi", "staged_regions", "typed_jit", "handlers", "kmap", "affine"}
EXTENSIONS = {".clj", ".cljc", ".edn", ".md", ".klr", ".lean", ".java", ".py", ".sh", ".json", ".csv", ".tsv", ".txt", ".tex", ".bib"}
IGNORED = {".git", ".internal", ".cpcache", "target", "classes", "__pycache__", "tmp", "node_modules"}


def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def intended(path):
    rel = path.relative_to(ROOT)
    if path.is_symlink() or any(part in IGNORED for part in rel.parts):
        return False
    if len(rel.parts) == 1:
        return rel.name in TOP
    if rel.parts[0] == "experiments":
        return len(rel.parts) > 2 and rel.parts[1] in EXPERIMENTS and rel.suffix in EXTENSIONS
    return rel.parts[0] in DIRECTORIES and rel.suffix in EXTENSIONS


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="target/artifact/klara-public-artifact.tar.gz")
    args = parser.parse_args()
    files = []
    for base, directories, names in os.walk(ROOT, followlinks=False):
        # Do not even traverse private working material or generated caches.
        directories[:] = [name for name in directories
                          if name not in IGNORED and not (Path(base) / name).is_symlink()]
        files.extend(path for name in names
                     if (path := Path(base) / name).is_file() and intended(path))
    files.sort()
    blobs = {str(path.relative_to(ROOT)): path.read_bytes() for path in files}
    manifest = {
        "format": "klara-public-artifact-1",
        "profile": "public-not-anonymized",
        "git_head": command("git", "rev-parse", "HEAD"),
        "working_tree_included": True,
        "files": {path: {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)} for path, data in blobs.items()},
        "verification": ["clojure -M:test", "clojure -M:verify"],
        "optional_checks": ["clojure -M:test-integration", "clojure -X:spec-diff"],
        "limits": ["source snapshot, not an offline dependency cache", "external spec/oracle dependencies described in doc/artifact.md",
                   "historical measurements retain their original source provenance", "no live JVM or authority checkpoint"],
    }
    manifest_bytes = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    blobs["ARTIFACT-MANIFEST.json"] = manifest_bytes
    output = Path(args.output)
    if not output.is_absolute():
        output = ROOT / output
    output.parent.mkdir(parents=True, exist_ok=True)
    # Fix both archive and gzip metadata so identical source snapshots have
    # identical bytes, independently of build time and output filename.
    with output.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for path, data in sorted(blobs.items()):
                    info = tarfile.TarInfo("klara/" + path)
                    info.size = len(data)
                    info.mtime = 0
                    info.mode = 0o644
                    archive.addfile(info, io.BytesIO(data))
    print(json.dumps({"path": str(output), "files": len(blobs), "bytes": output.stat().st_size,
                      "sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
                      "profile": manifest["profile"]}, indent=2))


if __name__ == "__main__":
    main()
