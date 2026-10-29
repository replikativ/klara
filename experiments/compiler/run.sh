#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
# Usage: experiments/compiler/run.sh [bench|profile|admission|hofs]
case "${1:-bench}" in
  bench) expression='(load-file "experiments/compiler/bench.clj") (klara.compile-bench/run!) (klara.compile-bench/steady!) (shutdown-agents)' ;;
  hofs) expression='(load-file "experiments/compiler/bench.clj") (alter-var-root (var klara.compile-bench/programs) select-keys [:hof-pipeline :hof-mapv]) (klara.compile-bench/run!) (klara.compile-bench/steady!) (shutdown-agents)' ;;
  admission) expression='(load-file "experiments/compiler/bench.clj") (load-file "experiments/compiler/profile.clj") (load-file "experiments/compiler/admission.clj") (klara.compile-admission/run!) (shutdown-agents)' ;;
  profile) expression='(load-file "experiments/compiler/bench.clj") (load-file "experiments/compiler/profile.clj") (klara.compile-profile/run!) (shutdown-agents)' ;;
  *) echo 'usage: experiments/compiler/run.sh [bench|profile|admission|hofs]' >&2; exit 2 ;;
esac
classes=$(mktemp -d /tmp/klara-s12-java.XXXXXX)
trap 'rm -rf "$classes"' EXIT
# Finish javac before starting Clojure: never two experiment JVMs at once.
javac -J-Xmx128m -d "$classes" experiments/compiler/java/klara/bench/Baselines.java
clojure -J-Xmx512m -J-XX:+UseSerialGC -Sdeps "{:paths [\"src\" \"$classes\"]}" -M -e \
  "$expression"
