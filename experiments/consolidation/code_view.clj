(ns consolidation.code-view
  "Reproduce guest structural regeneration, pruning and scope rejection."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.repl :as repl] [klara.world :as world] [klara.defs :as defs]
            [klara.code :as code] [klara.core :as core] [klara.compile.view :as view]
            [klara.stage :as stage]
            [klara.compile.staged]))

(defn id [c] (core/code-id (code/s->core (code/code-term c))))
(defn run-example []
  (let [s (repl/session {:source-roots ["examples/compat"]})
        r (repl/eval-response s "(require '[klara.residual]) (require '[klara.compiler]) (ns scratch) (def original (code (fn [x] (if false (/ 1 0) (let [y (+ x 1)] (* y y)))))) (def kernel (run original)) (def rebuilt (klara.residual/regenerate original)) (def pruned (klara.residual/prune-literal-branches original)) (klara.compiler/prepare-code rebuilt) (kernel 4)")
        _ (assert (empty? (:errors r)))
        _ (assert (.endsWith ^String (:output r) "25"))
        root (world/snapshot (repl/current-world s))
        [original rebuilt pruned] (mapv #(defs/lookup root %) ['scratch/original 'scratch/rebuilt 'scratch/pruned])
        inspected (view/inspect original)
        a (view/inspect original) b (view/inspect original)
        cursor (:at (first (:nodes a))) other-body (:code (second (:nodes b)))
        rejection (try (view/rebuild cursor [other-body]) :unexpected-success
                       (catch clojure.lang.ExceptionInfo e (select-keys (ex-data e) [:reason :check])))]
    (assert (pos? (:hits (stage/stats (:cache s)))))
    (assert (= (id original) (id rebuilt))) (assert (not= (id original) (id pruned)))
    (assert (= :scope (:check rejection)))
    {:scenario :bounded-code-regeneration :source-id (id original) :regenerated-id (id rebuilt)
     :pruned-id (id pruned) :pruned-form (code/code->form pruned)
     :installed-original-result 25 :native-entry-stats (stage/stats (:cache s)) :cross-view-rejection rejection
     :description (mapv #(select-keys % [:op :bindings :binding :scope :children :arity :name]) (:nodes inspected))
     :limits [:bounded-fragment :tested-bridge :no-general-correspondence-theorem
              :pruned-code-has-separate-entry-identity :cursors-not-durable-artifacts]}))

(defn -main [& _]
  (let [report (assoc (run-example) :source-sha256
                      (into {} (for [path (concat ["experiments/consolidation/code_view.clj"
                                                  "examples/compat/klara/residual.cljc"
                                                  "examples/compat/klara/compiler.cljc"]
                                                (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                 [path (core/sha256 (slurp path))])))
        output "target/code-view/result.edn"]
    (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
    (prn (select-keys report [:scenario :source-id :regenerated-id :pruned-id :installed-original-result :cross-view-rejection])))
  (shutdown-agents))
