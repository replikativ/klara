(ns baseline.entry-collision
  "Bounded forced CodeId-slot collision; run separately from entry timing."
  (:require [baseline.campaign :as metrics] [baseline.private-accumulator :as fixture]
            [clojure.pprint :as pp] [klara.core :as core] [klara.defs :as defs]
            [klara.eval :as ev] [klara.stage :as stage] [klara.world :as world]))

(defn- legacy-site []
  (let [table (object-array 512)]
    (fn [t]
      (let [implementation @#'core/code-id i (bit-and (System/identityHashCode t) 511)
            e (aget ^objects table i)]
        (if (and e (identical? t (nth e 0)) (identical? implementation (get e 2)))
          (nth e 1)
          (let [id (implementation t)] (aset ^objects table i [t id implementation]) id))))))

(defn run-probe! []
  (let [root (world/snapshot (world/make-world)) slot #(bit-and (System/identityHashCode %) 511)
        found (some (fn [i]
                      (let [f (defs/eval-form root fixture/source)
                            terms (vec (filter #(and (map? %) (= :fn (:op %)))
                                               (tree-seq coll? seq (ev/closure-term f))))]
                        (when (= (slot (first terms)) (slot (last terms)))
                          {:f f :terms terms :attempt i}))) (range 4096))
        _ (assert found "No colliding source found within the diagnostic budget")
        cache (stage/make-cache) v (ns-resolve 'klara.stage 'term-code-id) current @v
        observe (fn [implementation]
                  (with-redefs-fn {v implementation}
                    #(binding [ev/*basis* root ev/*mint* root]
                       (stage/with-cache cache
                         (binding [ev/*direct-hook* nil]
                           (dotimes [_ 64] (assert (true? (ev/call-value (:f found) [0 4 1]))))
                           (let [r (metrics/measure 128 (fn [] (ev/call-value (:f found) [0 4 1])))]
                             (assert (true? (:value r))) (dissoc r :value)))))))
        report {:scope :one-process-same-source-same-colliding-terms
                :attempt (:attempt found) :slots (mapv slot (:terms found)) :source fixture/source
                :legacy (observe (legacy-site)) :four-way (observe current)
                :limits [:forced-collision :single-order :diagnostic-not-a-language-speedup
                         :four-way-cache-still-has-capacity-misses]
                :source-sha256 (into {} (for [p ["src/klara/stage.clj" "src/klara/core.clj"
                                                "src/klara/eval.clj" "experiments/baseline/entry_collision.clj"]]
                                         [p (core/sha256 (slurp p))]))}]
    (spit "target/entry/collision-paired.edn" (with-out-str (pp/pprint report))) report))
