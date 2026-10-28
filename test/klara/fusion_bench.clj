(ns klara.fusion-bench
  "S3 measurements (not a test): generic T0 vs the fused executable
  (through the cache, guards included, and raw) vs wandler's a/defn vs
  plain clojure.core. Run from a REPL: (klara.fusion-bench/bench!)."
  (:require [klara.fusion :as f]
            [klara.fusion-test :as ft]
            [klara.stage :as s]
            [klara.defs :as d]
            [klara.world :as w]))

(defn- median-ms
  "Median wall time of thunk over n runs after warmup, in ms."
  [n thunk]
  (dotimes [_ (max 3 (quot n 2))] (thunk))
  (let [ts (sort (for [_ (range n)]
                   (let [t0 (System/nanoTime)] (thunk) (/ (- (System/nanoTime) t0) 1e6))))]
    (nth ts (quot n 2))))

(def cases
  {'sum-sq-even #(reduce + 0 (map (fn [x] (* x x)) (filter even? %)))
   'four-stage #(reduce + 0 (filter (fn [x] (< x 200)) (map (fn [x] (* x 3)) (filter odd? (map inc %)))))})

(defn bench! []
  (let [S (ft/session-with ft/pipelines)
        root (w/snapshot (:world S))
        cache (:cache S)]
    (doseq [[n] ft/pipelines] (f/optimize! S n))
    (vec
     (for [[n clj] cases
           size [1000 100000 1000000]
           :let [xs (vec (repeatedly size #(long (rand-int 100))))
                 pf (d/lookup root n)
                 exe (first (filter #(= (:code-id %) (klara.core/code-id (klara.eval/closure-term pf)))
                                    (s/executables cache)))
                 [wf] (ft/wandler-define! n (get ft/wandler-overrides n
                                                 (second (first (filter #(= n (first %)) ft/pipelines)))))
                 reps (if (> size 100000) 5 21)
                 expect (clj xs)]]
       (do (assert (= expect (pf xs) (s/with-cache cache (pf xs)) ((:run exe) xs)))
           (assert (== expect (wf xs)))
           {:pipeline n :n size
            :t0-generic-ms (median-ms (if (> size 100000) 3 reps) #(pf xs))
            :fused-via-cache-ms (median-ms reps #(s/with-cache cache (pf xs)))
            :fused-raw-ms (median-ms reps #((:run exe) xs))
            :wandler-ms (median-ms reps #(wf xs))
            :clojure-core-ms (median-ms reps #(clj xs))})))))
