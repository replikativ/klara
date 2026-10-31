(ns baseline.preparation
  "Phase attribution and matched single/repeated-production controls. No entry
   instrumentation or cached validation verdicts. Initial backend load is kept."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [baseline.private-accumulator :as fixture] [klara.compile.diagnostics :as diagnostics]
            [klara.compile.funding :as funding] [klara.compile.local-calls :as local]
            [klara.compile.staged :as staged] [klara.compile.ir :as ir]
            [klara.core :as core] [klara.defs :as defs] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as world]))

(defn- elapsed [f]
  (let [start (System/nanoTime) value (f)] {:value value :elapsed-ns (- (System/nanoTime) start)}))
(defn- median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))

(defn attempt
  ([root code f mode] (attempt root code f mode true))
  ([root code f mode traced?]
  (let [job (funding/create {})
        run (fn [] (let [prepare (elapsed (fn [] (staged/request root code
                                          {:job job :strategy 'policy :repeat-private-analysis? (= mode :repeat)})))
                 r (:value prepare) _ (assert (= :prepared (:status r)))
                 validation (elapsed (fn [] (staged/prevalidate (:candidate r))))
                 cache (stage/make-cache)
                 installation (elapsed (fn [] (staged/install! cache root (:value validation))))
                 _ (assert (= :installed (get-in installation [:value :status])))
                 value (binding [ev/*basis* root ev/*mint* root]
                         (stage/with-cache cache (ev/call-value f [100 4 10000])))
                 _ (assert (true? value))
                 exe (.-executable ^klara.compile.staged.Prepared (:candidate r))]
             {:mode mode :preparation-ns (:elapsed-ns prepare) :validation-ns (:elapsed-ns validation)
              :installation-ns (:elapsed-ns installation) :usage (funding/usage job)
              :source-nodes (count (ir/nodes (:generic exe))) :owned-nodes (count (ir/nodes (:ir exe)))
              :result value :cache-stats (stage/stats cache)}))
        captured (if traced? (diagnostics/capture run) {:value (run) :diagnostics {:enabled? false}})]
    (assoc (:value captured) :diagnostics (:diagnostics captured)))))

(defn- implementation-snapshot-pilot []
  ;; A cost probe for the rejected broad erasure-cache design, not a usable
  ;; dependency certificate or atomic snapshot of mutable host state.
  (let [names (loop [todo ['klara.compile.affine-erase 'klara.compile.private-accumulator 'clojure.core] seen #{}]
                (if-let [name (first todo)]
                  (if (seen name) (recur (next todo) seen)
                    (recur (concat (next todo) (map ns-name (vals (ns-aliases (the-ns name)))))
                           (conj seen name))) (vec (sort seen))))
        snapshots (mapv (fn [_]
                          (let [r (elapsed #(mapv (fn [name]
                                                  (let [n (the-ns name) vars (ns-interns n)]
                                                    [name (ns-aliases n) vars
                                                     (mapv (fn [[_ v]] [v (.getRawRoot ^clojure.lang.Var v)]) vars)])) names))]
                            {:elapsed-ns (:elapsed-ns r) :namespaces (count names)
                             :vars (reduce + (map #(count (nth % 2)) (:value r)))})) (range 3))]
    {:samples snapshots :scope :cost-pilot-only-not-a-complete-dependency-proof}))

(defn run-study! [label]
  (let [w (world/make-world) _ (local/bootstrap! w)
        _ (defs/define! w (list 'def 'policy fixture/policy-source))
        _ (defs/define! w (list 'def 'f fixture/source)) root (world/snapshot w)
        code (defs/eval-form root (list 'code fixture/source)) f (defs/lookup root 'f)
        first-use (attempt root code f :checked)
        attribution (mapv #(attempt root code f %) [:checked :repeat])
        pairs (mapv (fn [i] (let [order (if (even? i) [:checked :repeat] [:repeat :checked])]
                             {:order order :trials (mapv #(attempt root code f % false) order)})) (range 6))
        trials (mapcat :trials pairs)
        summary (into {} (for [mode [:checked :repeat]
                              :let [ts (filter #(= mode (:mode %)) trials)]]
                          [mode (into {} (for [metric [:preparation-ns :validation-ns :installation-ns]]
                                          [metric {:min (apply min (map metric ts))
                                                   :median (median (map metric ts)) :max (apply max (map metric ts))}]))]))
        report {:label label :java (System/getProperty "java.runtime.version")
                :source fixture/source :policy fixture/policy-source :first-use first-use
                :attribution attribution :pairs pairs :summary summary
                :implementation-snapshot-pilot (implementation-snapshot-pilot)
                :limits [:diagnostic-timing-only :nested-phase-times-inclusive :warm-pairs-uninstrumented :no-time-assertions
                         :fixed-source-one-input :rotating-warm-pairs :first-use-includes-lazy-backend-loading
                         :both-modes-use-the-same-artifact-and-ownership-checker
                         :repeat-control-is-original-production-plus-new-checker
                         :erasure-and-registry-validation-are-not-cached]
                :source-sha256 (into {} (for [path (concat ["experiments/baseline/preparation.clj"
                                                          "experiments/baseline/private_accumulator.clj"
                                                          "test/klara/compile/preparation_test.clj"]
                                                         (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                         [path (core/sha256 (slurp path))]))}
        path (str "target/preparation/" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (select-keys report [:label :summary])))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))) (shutdown-agents))
