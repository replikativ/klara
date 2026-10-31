(ns baseline.ownership-family
  "Persistent/owned JVM controls after checked helper exposure. Warm diagnostic,
   restricted value/error observers; no automatic full-host affine promotion."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [baseline.affine-composition :as affine-example]
            [klara.compile.analysis :as analysis] [klara.compile.baseline :as baseline]
            [klara.compile.budget :as budget] [klara.compile.compose :as compose]
            [klara.compile.infer-affine :as affine] [klara.compile.ir :as ir]
            [klara.compile.local-calls :as local] [klara.compile.staged :as staged]
            [klara.code :as code] [klara.core :as core] [klara.defs :as defs]
            [klara.eval :as ev] [klara.expand :as expand] [klara.stage :as stage] [klara.world :as world]))

(def cases
  {:captured-update
   {:form affine-example/source :layouts [:long :long] :arguments (fn [n] [n 3])}
   :branching-recurrence
   {:form '(fn [n bias]
             (let [step (fn [acc i]
                          (assoc (assoc (assoc acc 0 (+ (nth acc 1) bias))
                                        1 (nth acc 2)) 2 (+ (nth acc 0) i)))]
               (loop [i 0 acc [0 1 2]]
                 (if (< i n)
                   (if (< i bias) (recur (inc i) (step acc i))
                     (recur (+ i 2) (step acc i))) acc))))
    :layouts [:long :long] :arguments (fn [n] [n 3])}
   :histogram
   {:form '(fn [xs]
             (loop [i 0 counts [0 0 0 0]]
               (if (< i (count xs))
                 (let [k (nth xs i)]
                   (if (= k 0) (recur (inc i) (assoc counts 0 (inc (nth counts 0))))
                     (if (= k 1) (recur (inc i) (assoc counts 1 (inc (nth counts 1))))
                       (if (= k 2) (recur (inc i) (assoc counts 2 (inc (nth counts 2))))
                         (recur (inc i) (assoc counts 3 (inc (nth counts 3)))))))) counts)))
    :layouts [:long-vector] :arguments (fn [n] [(vec (take n (cycle [0 1 2 7])))])}})

(defn elapsed [f]
  (let [started (System/nanoTime) value (f)] {:value value :ns (- (System/nanoTime) started)}))

(defn prepare-case [definition]
  (let [w (world/make-world) _ (local/bootstrap! w) root (world/snapshot w)
        generic (expand/expand-expr (:form definition) root)
        b (budget/budget)
        exposure (elapsed #(compose/run b (ir/named generic)
                             (fn [t] (local/run b root t local/planner-symbol))
                             (fn [t] (binding [baseline/*budget* b] (baseline/scan! t budget/definition-limits))) 2))
        residual (analysis/indexed (get-in exposure [:value :term]))
        source (code/->code (code/core->s residual)) f (ev/run residual {:basis root})
        clj (elapsed #(binding [*ns* (the-ns 'baseline.ownership-family) *unchecked-math* false]
                         (eval (:form definition))))
        mandatory (elapsed #(staged/prepare root source {:backend :baseline}))
        owned (elapsed #(affine/prepare root source {:parameter-layouts (:layouts definition)}))
        engines (into {:clojure {:function (:value clj)}}
                      (for [[engine candidate] [[:baseline (:value mandatory)] [:owned (:value owned)]]
                            :let [cache (stage/make-cache)
                                  publication (elapsed #(staged/install! cache root (staged/prevalidate candidate)))]]
                        [engine {:function f :cache cache :publication-ns (:ns publication)}]))]
    {:engines engines :generic generic :residual residual :root root
     :original (ev/run generic {:basis root})
     :receipts (get-in exposure [:value :receipts])
     :owned-info (select-keys (staged/prepared-info (:value owned)) [:representations :checks-erased])
     :preparation {:helper-exposure-ns (:ns exposure) :inline-usage (budget/usage b)
                   :clojure-ns (:ns clj) :baseline-ns (:ns mandatory) :owned-ns (:ns owned)
                   :validation-installation-ns (into {} (for [[k p] engines :when (:cache p)] [k (:publication-ns p)]))}}))

(defn observe [prepared args]
  (let [run #(let [v (apply (:function prepared) args)]
               [:value (.getName (class v)) v
                (when (vector? v) (mapv (fn [x] (some-> x class .getName)) v))])]
    (try (if (:cache prepared) (stage/with-cache (:cache prepared) (run))
           (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil] (run)))
         (catch Throwable ex [:error (.getName (class ex)) (.getMessage ex)]))))

(defn sample [prepared args repetitions]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        thread (.threadId (Thread/currentThread))
        measure #(let [before (.getThreadAllocatedBytes bean thread) sink (volatile! nil)
                       timed (elapsed (fn [] (dotimes [_ repetitions] (vreset! sink (apply (:function prepared) args)))))]
                   {:value @sink :ns-per-call (/ (:ns timed) (double repetitions))
                    :bytes-per-call (/ (- (.getThreadAllocatedBytes bean thread) before) (double repetitions))})]
    (if (:cache prepared) (stage/with-cache (:cache prepared) (measure))
      (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil] (measure)))))

(defn run-study! [label]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        rows (mapv
               (fn [[name definition]]
                 (let [prepared (prepare-case definition) engines (:engines prepared)
                       names (vec (sort (keys engines)))
                       inputs (mapv (fn [n]
                                      (let [args ((:arguments definition) n)
                                            expected (:value (sample (:clojure engines) args 1))
                                            _ (dotimes [i 200]
                                                (doseq [k (take 3 (drop (mod i 3) (cycle names)))]
                                                  (assert (= expected (:value (sample (engines k) args 1))))))
                                            samples (mapv (fn [i] (into {} (for [k (take 3 (drop i (cycle names)))]
                                                                                 [k (sample (engines k) args 10)]))) (range 7))
                                            _ (assert (every? #(= expected (:value %)) (mapcat vals samples)))
                                            median #(nth (vec (sort %)) (quot (count %) 2))]
                                        {:n n :expected expected
                                         :engines (into {} (for [k names :let [rs (mapv k samples)]]
                                                             [k {:median-ns (median (map :ns-per-call rs))
                                                                 :median-bytes (median (map :bytes-per-call rs))
                                                                 :samples (mapv #(dissoc % :value) rs)}]))})) [100 1000 10000])
                       stats (into {} (for [[k p] engines :when (:cache p)] [k (stage/stats (:cache p))]))]
                   (doseq [[_ s] stats] (assert (pos? (:hits s))) (assert (zero? (:fallbacks s))))
                   {:name name :source (:form definition) :layouts (:layouts definition)
                    :source-id (core/code-id (:generic prepared)) :residual-id (core/code-id (:residual prepared))
                    :receipts (:receipts prepared) :owned-info (:owned-info prepared)
                    :preparation (:preparation prepared) :stats stats :inputs inputs}))
               (sort-by key cases))
        report {:label label :java (System/getProperty "java.runtime.version")
                :vm (System/getProperty "java.vm.name") :warmup 200 :samples 7 :batch 10 :rows rows
                :limits [:one-warm-process :current-thread-allocation :raw-input-layout-admission-included
                         :restricted-value-error-observations :host-identity-not-preserved
                         :ownership-preparation-not-in-the-inline-job-budget :no-cross-language-performance-claim]
                :source-sha256 (into {} (for [path (concat ["verification/baseline/ownership_family.clj"
                                                          "verification/baseline/affine_composition.clj"]
                                                         (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                        [path (core/sha256 (slurp path))]))}
        path (str "target/ownership-family/" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (mapv (fn [row] {:name (:name row) :preparation (:preparation row)
                    :inputs (mapv (fn [r] (update r :engines #(into {} (for [[k v] %] [k (dissoc v :samples)])))) (:inputs row))}) rows)))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))))

(defn evidence-study!
  "Separate histogram admission ablation on a reused immutable input. Evidence
   issuance is timed once; the evidence site checks remaining guards per call."
  [label]
  (let [p (prepare-case (:histogram cases)) n 10000
        args ((get-in cases [:histogram :arguments]) n) value (first args)
        owned (get-in p [:engines :owned])
        issued (elapsed #(stage/refine-argument :long-vector value)) evidence (:value issued)
        site (stage/make-evidence-site (:cache owned) (:function owned))
        evidence-entry {:function (fn [x]
                                   (when-not (identical? x (stage/evidence-value evidence))
                                     (throw (ex-info "evidence input differs" {})))
                                   (let [exe (site evidence (:root p) [])]
                                     (when-not exe (throw (ex-info "evidence admission declined" {})))
                                     ((:invoke1 exe) x)))}
        variants {:raw-owned-entry owned :evidence-owned-entry evidence-entry
                  :baseline (get-in p [:engines :baseline])}
        bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        _ (.setThreadAllocatedMemoryEnabled bean true)
        expected (vec (repeat 4 2500))
        _ (dotimes [_ 500] (doseq [[_ f] variants] (assert (= expected (:value (sample f args 1))))))
        samples (mapv (fn [_] (into {} (for [[k f] variants] [k (sample f args 20)]))) (range 7))
        _ (assert (every? #(= expected (:value %)) (mapcat vals samples)))
        report {:label label :n n :issuance-ns (:ns issued) :samples 7 :batch 20 :warmup 500
                :java (System/getProperty "java.runtime.version")
                :engines (into {} (for [k (keys variants) :let [rs (mapv k samples)
                                                               median #(nth (vec (sort %)) (quot (count %) 2))]]
                                    [k {:median-ns (median (map :ns-per-call rs))
                                        :median-bytes (median (map :bytes-per-call rs))
                                        :samples (mapv #(dissoc % :value) rs)}]))
                :limits [:separate-warm-cohort :same-immutable-input-reused
                         :issuance-cost-not-amortized-in-entry :remaining-guards-included
                         :restricted-observers :not-a-new-default-policy]
                :source-sha256 (into {} (for [path (concat ["verification/baseline/ownership_family.clj"]
                                                         (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                        [path (core/sha256 (slurp path))]))}
        path (str "target/ownership-family/evidence-" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (update report :engines #(into {} (for [[k v] %] [k (dissoc v :samples)])))))
