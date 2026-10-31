(ns baseline.loop-emission
  "Sequential experiment: ordinary loop lowering vs local recursive functions.
   with-redefs is diagnostic hosted glue, not a world-managed compiler pass."
  (:require [baseline.run :as base] [baseline.investment :as investment]
            [klara.compile.emit :as emit] [klara.compile.ir :as ir]
            [klara.compile.loop :as transfer] [klara.compile.speculate :as speculate]
            [klara.core :as core] [klara.expand :as expand] [klara.world :as world]
            [clojure.java.io :as io] [clojure.pprint :as pp]))

(def hosted-emit emit/emit-expr)

(defn direct-loop
  ([t env tail? self] (direct-loop t env tail? self false))
  ([t env tail? self consumed?]
   (if-let [{:keys [function self entry]} (when (= :letrec (:op t)) (transfer/view t))]
     (let [parameters (:params function)
           arguments (get-in entry [:node :args])
           initial (mapv #(emit/emit-expr % env false nil) arguments)
           temporaries (mapv (fn [_] (gensym "initial")) initial)
           loop-env (into (assoc env self {:recursive self :arity (:arity function)
                                           :parameters parameters})
                          (map (juxt identity identity) parameters))
           body (emit/emit-expr (:body function) loop-env true self)]
       `(let [~@(mapcat vector temporaries initial)]
          (loop [~@(mapcat vector parameters temporaries)] ~body)))
     (hosted-emit t env tail? self consumed?))))

(defn outcome [f n]
  (try (let [v (f n)] [:value (core/code-id v) v])
       (catch Throwable t [:error (.getName (class t))])))

(defn executable [form direct? checks?]
  (let [source (expand/expand-expr form world/empty-root)
        named (ir/named source)
        term (ir/lower (if checks? (:term (speculate/run named (core/code-id source))) named))
        run #(emit/run term #{} {} {:typed-loops? false})]
    (if direct? (with-redefs [emit/emit-expr direct-loop] (run)) (run))))

(defn check! []
  (mapv (fn [form]
          (let [reference (:value (base/prepare :clojure form))
                a (:run (executable form false false)) b (:run (executable form true false))
                inputs [nil false -1 0 1 5 7.0 7N]
                results (mapv (fn [n]
                                (let [expected (outcome reference n)]
                                  (assert (= expected (outcome a n) (outcome b n)))
                                  {:input n :outcome expected})) inputs)]
            {:source form :results results}))
        [(get-in investment/workloads [:loop :form])
         (get-in investment/workloads [:loop-carried-bound :form])
         (get-in investment/workloads [:recurrence :form])
         '(fn [n] (loop [i n a 1 b 2] (if (> i 0) (recur (dec i) b (+ a b)) a)))
         '(fn [n] (loop [i 0 sum n] (if (< i 3) (recur (inc i) (+ sum 1)) sum)))
         '(fn [n] (loop [i 0 sum 9223372036854775807]
                    (if (< i n) (recur (inc i) (+ sum 1)) sum)))]))

(defn measure [name n]
  (let [form (get-in investment/workloads [name :form])
        variants (into {:clojure (:value (base/prepare :clojure form))}
                       (for [[label direct? checks?] (concat [[:letfn false false] [:loop true false]]
                                                                            (when-not (= name :recurrence)
                                                                              [[:letfn-checks false true] [:loop-checks true true]]))]
                         [label (:run (executable form direct? checks?))]))
        expected ((:clojure variants) n)
        _ (doseq [[_ f] variants] (dotimes [_ 3000] (assert (= expected (f n)))))
        rows (mapv (fn [i]
                     (into {} (for [label (investment/rotated (vec (sort (keys variants))) i)]
                                [label (investment/sample {:value (get variants label)} n 100)]))) (range 9))]
    (assert (every? #(= expected (:value %)) (mapcat vals rows)))
    {:workload name :n n
     :engines (into {} (for [label (keys variants) :let [samples (mapv label rows)]]
                        [label {:median-ns (base/median (map :ns-per-call samples))
                                :median-bytes (base/median (map :bytes-per-call samples))
                                :samples (mapv #(dissoc % :value) samples)}]))}))

(defn -main [& [process]]
  (let [process (or process "0")
        bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        hashes (assoc (investment/source-hashes) "experiments/baseline/loop_emission.clj"
                      (core/sha256 (slurp "experiments/baseline/loop_emission.clj")))
        checks (check!)
        rows (mapv (fn [[name n]] (measure name n))
                   [[:loop 10000] [:loop-carried-bound 10000] [:recurrence 64]])
        report {:process process :java (System/getProperty "java.runtime.version")
                :source-sha256 hashes :checks checks :warmup 3000 :batch 100 :samples 9 :rows rows}
        output (str "target/investment/loop-emission-" process ".edn")]
    (assert (= hashes (assoc (investment/source-hashes) "experiments/baseline/loop_emission.clj"
                            (core/sha256 (slurp "experiments/baseline/loop_emission.clj")))))
    (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
    (doseq [r rows] (println (:workload r) (:n r)
                            (into {} (map (fn [[k v]] [k (select-keys v [:median-ns :median-bytes])])) (:engines r)))))
  (shutdown-agents))
