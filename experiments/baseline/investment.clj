(ns baseline.investment
  "Matched execution and preparation diagnostic. Run fresh JVMs sequentially."
  (:require [baseline.run :as base] [interpreter.bridge :as bridge]
            [interpreter.activation :as activation] [klara.compile.core :as compiler]
            [klara.compile.budget :as budget] [klara.compile.guest :as guest]
            [klara.compile.ir :as ir] [klara.compile.unbox :as unbox]
            [klara.compile.prepare :as preparation] [klara.core :as core]
            [klara.defs :as defs] [klara.eval :as ev] [klara.expand :as expand]
            [klara.stage :as stage] [klara.world :as world]
            [clojure.java.io :as io] [clojure.pprint :as pp])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]))

(def engines [:clojure :sci :t0 :nodes :activation :baseline :optimizing])
(def workloads
  (merge (into {} (map (fn [[k form]] [k {:form form :sizes [1000 10000]}])) base/workloads)
         {:tiny {:form '(fn [n] (+ n 1)) :sizes [1]}
          :branchy {:form '(fn [n] (let [y (+ n 1)] (if (< y 0) (- y) (* y y)))) :sizes [1]}
          :loop {:form (:loop base/workloads) :sizes [0 8 64 1000 10000]}
          ;; Same sum, but carry the invariant bound through the loop ABI.
          ;; This probes layout inference; it is not a new production rewrite.
          :loop-carried-bound {:form '(fn [n] (loop [i 0 sum 0 bound n]
                                               (if (< i bound)
                                                 (recur (inc i) (+ sum i) bound) sum)))
                               :sizes [64 10000]}
          :recurrence {:form '(fn [n] (loop [i n a [1] b [2]]
                                      (if (> i 0) (recur (dec i) b (conj a i)) a)))
                       :sizes [8 64 1000]}}))

(defn elapsed [f]
  (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        id (.threadId (Thread/currentThread))
        bytes (.getThreadAllocatedBytes bean id) t (System/nanoTime) value (f)]
    {:value value :ns (- (System/nanoTime) t)
     :bytes (- (.getThreadAllocatedBytes bean id) bytes)}))

(defn scope [prepared thunk]
  (if-let [cache (:cache prepared)]
    (stage/with-cache cache (thunk))
    (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil] (thunk))))

(defn compile-entry [root f mode]
  (let [b (budget/budget)
        emission (elapsed #(compiler/compile-def root 'subject {:mode mode :budget b}))
        exe (:value emission)
        validation (elapsed #(stage/validate-executable exe))
        cache (stage/make-cache)
        installation (elapsed #(stage/install-validated! cache (:value validation)))]
    {:value f :cache cache :executable exe
     :preparation {:compile (dissoc emission :value) :validation (dissoc validation :value)
                   :installation (dissoc installation :value) :usage (budget/usage b)
                   :pass-log (:pass-log exe) :transfer-receipts (:transfer-receipts exe)
                   :loop-layouts (mapv #(unbox/loop-kinds % {}) (filter #(= :letrec (:op %)) (ir/nodes (:ir exe))))
                   :total-ns (+ (:ns emission) (:ns validation) (:ns installation))}}))

(defn prepare [form process]
  (let [definition (elapsed #(let [w (world/make-world)]
                               (defs/define! w (list 'def 'subject form)) w))
        root (world/snapshot (:value definition)) f (:value (world/entry* root 'subject))
        term (expand/expand-expr form world/empty-root)
        ;; Rotate which compiler pays shared cold compiler/bootstrap costs.
        order (if (even? process) engines (vec (concat (take 5 engines) [:optimizing :baseline])))]
    {:definition (dissoc definition :value)
     :engines
     (into {} (for [engine order]
                [engine
                 (let [started (System/nanoTime)]
                  (try
                   (case engine
                     :baseline (compile-entry root f :baseline)
                     :optimizing (compile-entry root f :optimizing)
                     :t0 {:value f :preparation {:total-ns (:ns definition)}}
                     :clojure (let [p (base/prepare :clojure form)]
                                {:value (:value p) :preparation {:total-ns (:ns p)}})
                     :sci (let [p (base/prepare :sci form)]
                            {:value (:value p) :preparation {:total-ns (:ns p)}})
                     :nodes (let [p (elapsed #(bridge/prepare term))]
                              {:value #(bridge/invoke (:value p) %) :preparation (assoc (dissoc p :value) :total-ns (:ns p))})
                     :activation (let [p (elapsed #(activation/prepare term))]
                                   {:value #(bridge/invoke (:value p) %) :preparation (assoc (dissoc p :value) :total-ns (:ns p))}))
                   (catch clojure.lang.ExceptionInfo e
                     (if (or (#{:baseline :optimizing} engine)
                             (:decline (ex-data e)) (:bridge/decline (ex-data e)))
                       {:unsupported (merge {:message (ex-message e)} (ex-data e))
                        :preparation {:declined? true :total-ns (- (System/nanoTime) started)}}
                       (throw e)))))]))}))

(defn sample [prepared n repetitions]
  (scope prepared
         #(let [f (:value prepared) sink (volatile! nil)
                p (elapsed (fn [] (dotimes [_ repetitions] (vreset! sink (f n))))) ]
            {:ns-per-call (/ (:ns p) (double repetitions))
             :bytes-per-call (/ (:bytes p) (double repetitions)) :value @sink})))

(defn rotated [active i] (take (count active) (drop (mod i (count active)) (cycle active))))

(defn entry-study [all n expected]
  (when-let [prepared (when (:executable (:baseline all)) (:baseline all))]
    (let [cache (:cache prepared) f (:value prepared) body (:run (:executable prepared))
          variants {:session prepared :clojure (:clojure all) :sci (:sci all)
                    :optimizing (:optimizing all)
                    :host-entry {:value #(stage/with-cache cache (f %))}
                    ;; Diagnostic only: bypasses admission/guards. Use only the
                    ;; matched immutable primitive-only input cohort here.
                    :body {:value body}}]
      (doseq [[_ p] variants] (scope p #(dotimes [_ 2000] (assert (= expected ((:value p) n))))))
      (into {} (for [[name p] variants]
                 [name (let [samples (mapv (fn [_] (sample p n 100)) (range 9))]
                         (assert (every? #(= expected (:value %)) samples))
                         {:median-ns (base/median (map :ns-per-call samples))
                          :median-bytes (base/median (map :bytes-per-call samples))
                          :samples (mapv #(dissoc % :value) samples)})])))))

(defn workload [process [name {:keys [form sizes]}]]
  (println :starting name) (flush)
  (let [p (prepare form process) prepared (:engines p)
        active (filterv #(get-in prepared [% :value]) engines)
        rows (mapv (fn [n]
             (let [expected ((get-in prepared [:clojure :value]) n)
                   first-calls (into {} (for [e active :let [p (get prepared e)
                                                              r (elapsed #(scope p (fn [] ((:value p) n))))]]
                                          (do (assert (= expected (:value r))) [e (dissoc r :value)])))
                   _ (dotimes [i 200]
                       (doseq [e (rotated active (+ i process)) :let [p (get prepared e)]]
                         (scope p #(assert (= expected ((:value p) n))))))
                   samples (mapv (fn [i] (into {} (for [e (rotated active (+ i process))]
                                                                  [e (sample (get prepared e) n (if (< n 100) 100 5))]))) (range 9))
                   _ (assert (every? #(= expected (:value %)) (mapcat vals samples)))
                   row {:n n :expected-id (core/code-id expected) :first-calls first-calls
                        :engines (into {} (for [e active :let [s (mapv e samples)]]
                                           [e {:median-ns (base/median (map :ns-per-call s))
                                               :median-bytes (base/median (map :bytes-per-call s))
                                               :samples (mapv #(dissoc % :value) s)}]))}]
               (println name n (into {} (map (fn [[e v]] [e (:median-ns v)])) (:engines row))) (flush)
               row)) sizes)]
    {:workload name :source form :definition (:definition p)
     :preparation (into {} (map (fn [[e p]] [e (cond-> (:preparation p)
                                                   (:unsupported p) (assoc :unsupported (:unsupported p)))])) prepared)
     :rows rows
     ;; Do not give baseline extra warmup before the matched rows finish.
     :entry-studies (when-let [sizes (case name :tiny [1] :loop [64 10000]
                                          :loop-carried-bound [10000] :recurrence [64] nil)]
                      (into {} (for [n sizes]
                                 [n (entry-study prepared n ((get-in prepared [:clojure :value]) n))])))
     :cache-stats (into {} (keep (fn [[e p]] (when (:cache p) [e (stage/stats (:cache p))]))) prepared)}))

(defn budget-study []
  (let [w (world/make-world)]
    (doseq [form ['(def good (fn [x] (+ x 1))) '(def bad (fn [x] (code (+ x 1))))]] (defs/define! w form))
    (mapv (fn [limits]
            (let [job (preparation/job {:session-limits limits}) cache (stage/make-cache)
                  p (elapsed #(preparation/prepare! job (world/snapshot w)
                                                   [{:name 'bad :file :one} {:name 'good :file :one}
                                                    {:name 'good :file :two}] cache))]
              {:limits limits :cost (dissoc p :value) :report (:value p)}))
          [{:work 0} {:emissions 0} {:emissions 1} {}])))

(defn repeat-preparation-study []
  (mapv (fn [name]
          (let [w (world/make-world) form (get-in workloads [name :form])
                _ (defs/define! w (list 'def 'subject form))
                root (world/snapshot w) f (:value (world/entry* root 'subject))]
            {:workload name :source-id (core/code-id (ev/closure-term f))
             :attempts (mapv (fn [_]
                               (into {} (for [mode [:baseline :optimizing]]
                                          [mode (:preparation (compile-entry root f mode))]))) (range 5))}))
        [:tiny :loop :loop-carried-bound :recurrence]))

(defn source-hashes []
  (into {} (for [p (concat ["deps.edn" "experiments/baseline/run.clj" "experiments/baseline/investment.clj"
                            "experiments/interpreter/bridge.clj" "experiments/interpreter/mutable.clj"
                            "experiments/interpreter/activation.clj"]
                          (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
             [p (core/sha256 (slurp p))])))

(defn -main [& [process]]
  (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil ev/*reference-driver* false]
    (let [bean ^ThreadMXBean (ManagementFactory/getThreadMXBean)
          _ (.setThreadAllocatedMemoryEnabled bean true)
          process (Long/parseLong (or process "0"))
          hashes (source-hashes)
          ;; Let bindings make setup order explicit: budget experiments must
          ;; not silently warm the compiler before the matched cohort.
          started (System/nanoTime)
          rows (mapv #(workload process %) (sort-by key workloads))
          repeated (repeat-preparation-study)
          budgets (budget-study)
          report {:process process :java (System/getProperty "java.runtime.version")
                  :vm (System/getProperty "java.vm.name") :vendor (System/getProperty "java.vendor")
                  :clojure (clojure-version) :sci "0.15.59"
                  :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
                  :measurement {:warmup 200 :samples 9 :small-batch 100 :large-batch 5
                                :cache-scope :per-sample :order :rotating
                                :entry-study {:warmup 2000 :samples 9 :batch 100}}
                  :workloads rows :repeated-preparation repeated :budgets budgets
                  :experiment-ns (- (System/nanoTime) started)
                  :source-sha256 hashes}
          output (str "target/investment/run-" process ".edn")]
      (assert (= hashes (source-hashes)) "Source changed during measurement")
      (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
      (println :report output)))
  (shutdown-agents))
