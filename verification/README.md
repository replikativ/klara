# Maintained verification

`clojure -M:verify` runs the restricted Ansatz models, implementation bridges
and scenario regressions here. Namespace names are preserved across promotion
from `experiments/`; theorem names and model identities are unchanged.
Run `clojure -M:test` **and** `clojure -M:verify` for the release gate. Core
regressions are no longer executed a second time by verification. Shared test
sources live in `test/klara/compile/support.clj`; independent checkers remain
independent. `clojure -M:runtime-refinement` exercises the optional interpreter
models and their experimental engines.

Reports are generated under `target/verification/`. Historical frozen source
manifests retain original paths and hashes; active paths moved without renaming
namespaces. Historical benchmark code is under `experiments/history/` and is
available explicitly through `-M:history`.
