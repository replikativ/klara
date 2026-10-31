(ns consolidation.world-compiler
  "Reproduce world-managed staged compiler evolution without timing claims."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.repl :as repl] [klara.world :as world] [klara.defs :as defs]
            [klara.compile.core :as compiler] [klara.compile.budget :as budget]
            [klara.compile.service :as service] [klara.compile.guest :as guest]
            [klara.compile.staged] [klara.core :as core] [klara.stage :as stage]))

(defn- receipts [exe]
  (mapv #(select-keys % [:producer :producer-symbol :producer-code-id
                         :policy-symbol :policy-code-id :service-transitions :compiler-reads])
        (:transfer-receipts exe)))

(defn run-example []
  (let [s (repl/session {:source-roots ["examples/compat"]})
        loaded (repl/eval-response s "(require '[klara.compiler]) (ns scratch) (defn kernel [n] (loop [i n a 1 b 2] (if (> i 0) (recur (dec i) b (+ a b)) a)))")
        _ (assert (empty? (:errors loaded)))
        w (repl/current-world s) root (world/snapshot w)
        counts (into {} (for [sym ['klara.compiler/transfer 'klara.compiler/three]
                             :let [r (service/invoke (budget/budget) root sym
                                                     [['i 'a 'b] ['one 'two 'three]] 4096)]]
                         [sym (select-keys r [:value :transitions])]))
        _ (assert (= (get-in counts ['klara.compiler/transfer :value])
                     (get-in counts ['klara.compiler/three :value])))
        b (budget/budget) before (compiler/compile-def root 'scratch/kernel {:mode :baseline :budget b})
        prepared (repl/eval-response s "(klara.compiler/prepare-three)")
        _ (assert (empty? (:errors prepared)))
        after (compiler/compile-def root 'scratch/kernel {:mode :baseline})
        _ (assert (= :world-stepped (-> after :transfer-receipts first :producer)))
        _ (stage/install! (:cache s) after)
        result (repl/eval-string s "(scratch/kernel 5)")
        _ (assert (= "13" result))
        child (world/fork w)
        _ (defs/define! child (list 'def guest/policy-symbol '(fn [request] :hosted)))
        child-exe (compiler/compile-def child 'scratch/kernel {:mode :baseline})
        _ (defs/define! child (list 'def guest/policy-symbol '(fn [request] 'klara.compiler/three)))
        _ (defs/define! child '(def klara.compiler/three (fn [destinations arguments] {})))
        rejection (try (compiler/compile-def child 'scratch/kernel {:mode :baseline}) :unexpected-success
                       (catch clojure.lang.ExceptionInfo e (select-keys (ex-data e) [:reason :check])))
        still-runs (stage/with-cache (:cache s) (defs/eval-form (world/snapshot child) '(scratch/kernel 5)))
        parent-exe (compiler/compile-def root 'scratch/kernel {:mode :baseline})]
    (assert (map? rejection)) (assert (= 13 still-runs))
    {:scenario :world-managed-staged-transfer :kernel-code-id (:code-id before)
     :direct-service-transitions (into {} (map (fn [[sym r]] [sym (:transitions r)])) counts)
     :before (receipts before) :after-ordinary-service-preparation (receipts after)
     :preparation-usage (budget/usage b) :ordinary-service-preparation (:output prepared)
     :kernel-result result :fork-policy-choice (receipts child-exe)
     :invalid-child-service rejection :installed-kernel-after-rejection still-runs
     :parent-unchanged (receipts parent-exe)
     :limits [:finite-example :tested-bridge :no-new-universal-theorem
              :compiler-services-remain-stepped-unless-reviewed :no-timing-claim]}))

(defn -main [& _]
  (let [report (assoc (run-example)
                      :source-sha256
                      (into {} (for [path (concat ["experiments/consolidation/world_compiler.clj"
                                                  "examples/compat/klara/compiler.cljc"]
                                                (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                 [path (core/sha256 (slurp path))])))
        path "target/world-compiler/result.edn"]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (prn (select-keys report [:scenario :direct-service-transitions :kernel-result
                              :invalid-child-service :installed-kernel-after-rejection])))
  (shutdown-agents))
