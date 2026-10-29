(load-file "experiments/pldi/smc.clj")
(load-file "experiments/affine/bench.clj")
(require '[klara.authority :as a] '[klara.pldi.smc :as smc]
         '[klara.world :as w] '[klara.defs :as d] '[klara.compile.core :as cc] '[klara.stage :as s])
(let [original a/op!
      count-ops (fn [run]
                  (let [ops (atom {}) result (with-redefs [a/op! (fn [op args frames]
                                                                                (swap! ops update op (fnil inc 0))
                                                                                (original op args frames))]
                                                   (run))]
                    {:result result :dispatches @ops :total (reduce + (vals @ops))}))
      records (vec
               (concat
                 (for [mode [:dynamic :erased]]
                   (let [{:keys [cache run]} (smc/setup mode)
                         r (count-ops #(s/with-cache cache (run)))]
                     (assert (= (if (= mode :dynamic) 6912 0) (:total r)))
                     (assoc r :workload :smc :mode mode :particle-observations 384)))
                 (for [mode [:dynamic :erased]]
                   (let [wo (w/make-world) cache (s/make-cache)
                         _ (d/define! wo klara.affine-bench/program)
                         _ (when (= mode :erased) (s/install! cache (cc/compile-def wo 'counter)))
                         f (d/lookup (w/snapshot wo) 'counter)
                         r (count-ops #(binding [a/*store* (a/new-store)] (s/with-cache cache (f 1000))))]
                     (assert (= [1000] (:result r)))
                     (assert (= (if (= mode :dynamic) 1002 0) (:total r)))
                     (assoc r :workload :affine-loop :mode mode :updates 1000))))) ]
  (spit (str (first *command-line-args*) "/authority-dispatch.edn") (pr-str records))
  (prn records))
(shutdown-agents)
