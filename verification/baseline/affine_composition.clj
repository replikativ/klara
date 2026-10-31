(ns baseline.affine-composition
  "Exploratory staged-inline -> ownership handoff under the private observation
   contract. Explicitly records the host identity counterexample. No new recipe."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.compile.analysis :as analysis] [klara.compile.budget :as budget]
            [klara.compile.infer-affine :as affine] [klara.compile.ir :as ir]
            [klara.compile.local-calls :as local] [klara.compile.staged :as staged]
            [klara.code :as code] [klara.core :as core] [klara.eval :as ev]
            [klara.expand :as expand] [klara.world :as world] [klara.stage :as stage]))

(def source
  '(fn [n bias]
     (let [step (fn [acc i]
                  (assoc (assoc acc 0 (+ (nth acc 0) i))
                         1 (+ (nth acc 1) bias)))]
       (loop [i 0 acc [0 0]]
         (if (< i n) (recur (inc i) (step acc i)) acc)))))

(defn- observation [f args cache]
  (try (let [v (stage/with-cache cache (ev/call-value f args))]
         [:value (.getName (class v)) v
          (when (vector? v) (mapv #(some-> % class .getName) v))])
       (catch Throwable e [:error (.getName (class e)) (.getMessage e)])))

(defn run-example []
  (let [w (world/make-world) _ (local/bootstrap! w) root (world/snapshot w)
        original-core (expand/expand-expr source root)
        original (ev/run original-core {:basis root})
        before (try (affine/infer original-core) :unexpected
                    (catch clojure.lang.ExceptionInfo e (ex-data e)))
        _ (assert (= :scope (:check before)))
        b (budget/budget)
        inlined (local/run b root (ir/named original-core) local/planner-symbol)
        residual-core (analysis/indexed (:term inlined))
        residual-code (code/->code (code/core->s residual-core))
        residual (ev/run residual-core {:basis root})
        inferred (affine/infer residual-core)
        prepared (staged/prevalidate (affine/prepare root residual-code))
        info (staged/prepared-info prepared) cache (stage/make-cache)
        _ (staged/install! cache root prepared)
        cases (mapv (fn [args]
                       (let [expected (observation original args (stage/make-cache))
                             actual (observation residual args cache)]
                         (assert (= expected actual))
                         {:arguments args :observation actual}))
                    [[0 1] [1 2] [5 3] [100 4] [3 -2] [2 Long/MAX_VALUE]])
        _ (assert (pos? (:hits (stage/stats cache))))
        _ (assert (zero? (:fallbacks (stage/stats cache))))
        first-result (stage/with-cache cache (ev/call-value residual [3 1]))
        _ (stage/with-cache cache (ev/call-value residual [10 2]))
        _ (assert (= [3 3] first-result))
        ;; The private fragment's observation relation excludes arbitrary host
        ;; identity. This concrete counterexample prevents upgrading it silently
        ;; to a claim about all Clojure/host observers.
        original-pair [(ev/call-value original [0 1]) (ev/call-value original [0 1])]
        owned-pair (stage/with-cache cache [(ev/call-value residual [0 1])
                                            (ev/call-value residual [0 1])])]
    {:scenario :staged-inline-to-owned-accumulator :source source
     :before-inlining before :inline-receipt (:receipt inlined)
     :original-code-id (core/code-id original-core) :residual-code-id (core/code-id residual-core)
     :ownership-facts (:facts inferred) :representations (:representations info)
     :checks-erased (:checks-erased info) :cases cases :retained-result first-result
     :host-identity-counterexample {:original-shares-zero-iteration-result (identical? (first original-pair) (second original-pair))
                                    :owned-shares-zero-iteration-result (identical? (first owned-pair) (second owned-pair))
                                    :equal-values (= (first original-pair) (first owned-pair))}
     :native-entry-stats (stage/stats cache) :inline-usage (budget/usage b)
     :limits [:restricted-value-error-observations :host-identity-not-preserved
              :residual-has-separate-entry-identity :hosted-ownership-analysis
              :no-new-semantic-proof :no-allocation-or-throughput-claim]}))

(defn run-study! [label]
  (let [report (assoc (run-example) :source-sha256
                      (into {} (for [path (concat ["verification/baseline/affine_composition.clj"]
                                                 (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                 [path (core/sha256 (slurp path))])))
        path (str "target/affine-composition/" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (select-keys report [:scenario :before-inlining :ownership-facts :host-identity-counterexample
                        :native-entry-stats :inline-usage])))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))))
