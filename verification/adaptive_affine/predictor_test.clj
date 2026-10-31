(ns adaptive-affine.predictor-test
  (:require [clojure.test :refer [deftest is]]
            [adaptive-affine.predictor :as p]
            [klara.world :as w])
  (:import [java.util.concurrent Executors TimeUnit]))

(deftest learned-outcomes-are-advisory
  (let [model (reduce #(p/train-one %1 0 %2) {} [:left :left :right])]
    (is (= :left (p/predict model 0)))
    (is (= :right (p/predict (reduce #(p/train-one %1 0 %2) model (repeat 8 :right)) 0)))))

(deftest isolated-results-need-the-exact-validated-class
  (let [ctx (p/context) before (w/snapshot (:world ctx))
        candidate (:value (p/isolated-follow ctx :left 32))]
    (is (= [8 24] (:result candidate)))
    (is (p/valid? ctx :left candidate))
    (is (not (p/valid? ctx :right candidate)))
    (is (not (p/valid? ctx :left (assoc candidate :basis w/empty-root))))
    (is (w/entry* (:root candidate) 'speculative-result))
    (is (nil? (w/entry* before 'speculative-result)))
    (is (identical? before (w/snapshot (:world ctx))))))

(deftest hit-and-miss-both-return-the-real-continuation
  (let [ctx (p/context) worker (Executors/newSingleThreadExecutor)]
    (try
      (let [model {0 {:left 10}}
            hit (p/speculation-step worker ctx model {:site 0 :seed 0} 1000 32)
            miss (p/speculation-step worker ctx model {:site 0 :seed 1} 1000 32)]
        (is (:hit? hit))
        (is (false? (:hit? miss)))
        (is (= [8 24] (:value hit)))
        (is (= [24 8] (:value miss)))
        (is (= 0 (:fallback-ns hit)))
        (is (pos? (:fallback-ns miss)))
        (is (= 0 (:wasted-worker-cpu-ns hit)))
        (is (pos? (:wasted-worker-cpu-ns miss))))
      (finally (.shutdown worker) (.awaitTermination worker 30 TimeUnit/SECONDS)))))
