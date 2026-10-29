(load-file "experiments/compiler/bench.clj")
(load-file "experiments/pldi/smc.clj")
(load-file "experiments/pldi/worker.clj")
(apply klara.pldi.worker/run (let [[mode path] *command-line-args*] [(keyword mode) path]))
