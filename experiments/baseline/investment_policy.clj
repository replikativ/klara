(ns baseline.investment-policy
  "Finite traces compare four preparation policies, including cold/losing work."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.compile.investment :as investment] [klara.compile.local-calls :as local]
            [klara.compile.private-accumulator] [klara.compile.funding :as funding]
            [klara.compile.staged :as staged] [klara.core :as core] [klara.defs :as defs]
            [klara.eval :as ev] [klara.stage :as stage] [klara.world :as world]
            [baseline.private-accumulator :as fixture] [baseline.campaign :as metrics]))

(def helper '(fn [n] (let [step (fn [x] (+ x 3))]
                      (loop [i 0 total 0]
                        (if (< i n) (recur (inc i) (+ total (step i))) total)))))
(def held-out '(fn [n] (let [step (fn [x] (if (< x 8) (+ x 3) (- x 2)))]
                        (loop [i 0 total 1]
                          (if (< i n) (recur (inc i) (+ total (step i))) total)))))
(def workloads
  [{:id :short-helper :source helper :segments [[12 [0]]] :variant :baseline :estimate-ns 8000000}
   {:id :hot-helper :source helper :segments [[1024 [32]]] :variant :baseline :estimate-ns 8000000}
   {:id :held-out-branch :source held-out :segments [[1024 [32]]] :variant :baseline :estimate-ns 8000000}
   {:id :hot-private :source fixture/source :segments [[1024 [32 4 10000]]] :variant :private :estimate-ns 30000000}
   {:id :layout-shift :source fixture/source :segments [[64 [32 4 10000]] [960 [32.5 4 10000]]]
    :variant :private :estimate-ns 30000000}])
(def modes [:never :always :threshold :bounded])
(defn- elapsed [f]
  (let [r (metrics/measure 1 f)]
    {:value (:value r) :ns (long (:wall-ns-per-call r))
     :cpu-ns (:cpu-ns-per-call r) :bytes (:bytes-per-call r)}))
(defn- preparation-options [workload]
  (merge {:selection {:variant (:variant workload) :priority 10}}
         (if (= :private (:variant workload)) {:strategy 'policy} {:local-call-planner local/planner-symbol})))
(defn- eager! [cache root source job opts]
  (let [result (elapsed #(let [r (staged/request root source (assoc opts :job job))]
                          (if (= :prepared (:status r))
                            (staged/install! cache root (staged/prevalidate (:candidate r)))
                            (select-keys r [:status :reason]))))]
    {:status (get-in result [:value :status]) :reason (get-in result [:value :reason])
     :spent-ns (:ns result) :usage (funding/usage job)}))

(defn run-trace [workload mode]
  (let [setup
        (elapsed #(let [w (world/make-world)]
                    (local/bootstrap! w) (investment/bootstrap! w)
                    (defs/define! w (list 'def 'policy fixture/policy-source))
                    (defs/define! w (list 'def 'f (:source workload)))
                    (let [root (world/snapshot w)]
                      {:world w :root root :f (defs/lookup root 'f)
                       :source (defs/eval-form root (list 'code (:source workload)))})))
        {:keys [world root f source]} (:value setup)
        arguments (vec (mapcat (fn [[n args]] (repeat n args)) (:segments workload)))
        ;; Independent host oracle is outside application traces, reported as
        ;; experimental setup rather than silently charged to one policy.
        oracle (elapsed #(let [host (binding [*ns* (the-ns 'baseline.investment-policy)] (eval (:source workload)))]
                           (into {} (for [args (distinct arguments)] [args (apply host args)]))))
        cache (stage/make-cache) job (funding/create {}) opts (preparation-options workload)
        shift-points (set (rest (reductions + 0 (map first (:segments workload)))))
        trace
        (elapsed
          (fn [] (loop [i 0 execution-ns 0 investments []]
             (if (= i (count arguments))
               {:execution-ns execution-ns :investments investments}
               (let [args (nth arguments i)
                     checkpoint? (case mode :never false :always (= i 0) :threshold (= i 8)
                                   :bounded (or (= i 8) (contains? shift-points i)))
                     r (when checkpoint?
                         (if (= mode :bounded)
                           (let [measured (elapsed #(investment/attempt! cache root 'f args job
                                                     {:remaining-calls (- (count arguments) i) :allowance-ns 200000000
                                                      :preparation-estimate-ns (:estimate-ns workload)
                                                      :preparation-options opts}))]
                             (assoc (:value measured) :attempt-wall-ns (:ns measured)))
                           (eager! cache root source job opts)))
                     call (binding [ev/*basis* root ev/*mint* root]
                            (elapsed (fn [] (stage/with-cache cache (ev/call-value f args)))))]
                 (assert (= (get (:value oracle) args) (:value call)))
                 (recur (inc i) (+ execution-ns (:ns call))
                        (cond-> investments r (conj (assoc r :at i :arguments args)))))))))]
    (assert (identical? root (world/snapshot world)))
    {:workload (:id workload) :mode mode :calls (count arguments)
     :setup-ns (:ns setup) :oracle-ns (:ns oracle) :trace-wall-ns (:ns trace)
     :trace-cpu-ns (:cpu-ns trace) :trace-allocated-bytes (:bytes trace)
     :execution-ns (get-in trace [:value :execution-ns])
     :investment-ns (reduce + (map #(or (:attempt-wall-ns %) (:spent-ns %)) (get-in trace [:value :investments])))
     :investments (get-in trace [:value :investments]) :usage (funding/usage job)
     :stats (stage/stats cache) :source (:source workload) :segments (:segments workload)}))

(defn run-study! [label offset]
  (let [rows (vec (mapcat (fn [[i workload]]
                           (mapv #(run-trace workload %)
                                 (take 4 (drop (mod (+ i offset) 4) (cycle modes)))))
                         (map-indexed vector workloads)))
        report {:label label :java (System/getProperty "java.runtime.version") :rows rows
                :forecasts {:baseline-preparation-ns 8000000 :private-preparation-ns 30000000
                            :provenance :fixed-advisory-estimates-not-fitted-to-these-traces
                            :candidate-fraction 0.5 :safety-factor 2.0 :threshold-calls 8}
                :limits [:bounded-five-scenarios :one-sequential-process-per-report :mode-order-rotates
                         :preparation-probes-validation-publication-in-trace :extra-probes-do-not-consume-application-inputs
                         :source-and-oracle-setup-separate :process-startup-separate
                         :shared-host-jit-gc-clock :no-autonomous-profiler-or-retirement
                         :short-noisy-probes :horizon-is-a-forecast :no-profitability-assertions]
                :source-sha256 (into {} (for [p (concat ["experiments/baseline/investment_policy.clj"
                                                        "verification/consolidation/indexed_binding.clj"
                                                        "test/klara/compile/inline_check_test.clj"
                                                        "test/klara/compile/investment_test.clj"]
                                                       (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                         [p (core/sha256 (slurp p))]))}
        path (str "target/investment-policy/" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    {:label label :rows (mapv #(select-keys % [:workload :mode :trace-wall-ns :investment-ns]) rows)}))
(defn -main [& [label offset]] (prn (run-study! (or label "fresh") (if offset (Long/parseLong offset) 0))) (shutdown-agents))
