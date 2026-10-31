# Historical experiments

These coherent source/result bundles informed the current compiler. They are
retained for attribution, failed cases and reproducibility, not the current
implementation route. `:history` adds the historical namespace root; for aligned
modules use `clojure -M:history -m <original.namespace>`. Older scripts with
file/namespace mismatches retain explicit `load-file` drivers. In particular,
run `bash experiments/history/compiler/run.sh` for its Java baseline setup. Historical commands/results describe the versions
that produced them; they do not establish current performance. Maintained
models and bridge tests are in `verification/`; active benchmark drivers remain
in `experiments/baseline` and `experiments/interpreter`.
