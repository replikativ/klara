(ns adaptive-affine.review
  "Emitter review; preserves S25's original artifacts. Load bench.clj first."
  (:refer-clojure :exclude [run!])
  (:require [adaptive-affine.bench :as b]
            [clojure.pprint :as pp]
            [clojure.walk :as walk]
            [klara.compile.infer-affine :as ia]
            [klara.compile.staged :as staged]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w]))

(defn run! []
  (let [world (b/load-world) root (w/snapshot world)
        source (d/lookup root 'counter-code) closure (d/lookup root 'counter)
        candidate (ia/prepare root source) info (staged/prepared-info candidate)
        cache (stage/make-cache) _ (staged/install! cache root candidate)
        primitive (eval (:form info))
        ;; Reproduce the old setter, preserving type metadata on the forms.
        legacy (eval (walk/postwalk #(if (= 'aset %) 'aset-long %) (:form info)))
        functions [[:functional b/functional] [:transient b/transient-counter]
                   [:legacy-array legacy] [:primitive-array primitive]
                   [:guarded #(stage/with-cache cache (ev/call-value closure [%1 %2]))]]
        sizes [32 256 1024 4096]
        _ (doseq [n sizes [_ f] functions] (dotimes [_ 3000] (f n (quot n 3))))
        rows (mapv
               (fn [n]
                 ;; Alternate order between batches, retain all samples.
                 (let [samples
                       (reduce
                         (fn [out batch]
                           (reduce
                             (fn [out [label f]]
                               (let [m (b/measure 500 1 #(f n (quot n 3)))]
                                 (assert (= [(quot n 3) (- n (quot n 3))] (:value m)))
                                 (update out label (fnil into []) (:samples m))))
                             out (if (even? batch) functions (reverse functions))))
                         {} (range 7))]
                   {:n n :measurements
                    (update-vals samples
                      (fn [xs] {:median-ns (b/median (map :ns xs))
                                :median-bytes (b/median (map :bytes xs)) :samples xs}))}))
               sizes)
        report {:java (System/getProperty "java.runtime.version")
                :change :reflective-aset-long-to-typed-aset
                :rows rows
                :limitations [:single-process :already-warm-jvm :no-cold-start
                              :thread-allocation-not-retained-memory
                              :no-controller-or-preparation-amortization]}]
    (spit "experiments/adaptive_affine/review-results.edn" (with-out-str (pp/pprint report)))
    (spit "experiments/adaptive_affine/review-residual.clj.txt" (with-out-str (pp/pprint (:form info))))
    (pp/pprint (update report :rows
                #(mapv (fn [row] (update row :measurements
                                  (fn [ms] (update-vals ms (fn [m] (dissoc m :samples)))))) %)))
    report))
