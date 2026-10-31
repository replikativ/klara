(ns baseline.ownership-family-test
  (:require [clojure.test :refer [deftest is]] [baseline.ownership-family :as family]
            [klara.compile.infer-affine :as affine] [klara.expand :as expand]
            [klara.world :as world]))

(deftest branch-update-and-histogram-families-match-admitted-observers
  (doseq [[name definition] family/cases
          :let [p (family/prepare-case definition)]]
    (is (seq (get-in p [:owned-info :representations])) (str name))
    (doseq [n [0 1 2 7 31] :let [args ((:arguments definition) n)
                                expected (family/observe {:function (:original p)} args)]]
      (doseq [[engine f] (:engines p)]
        (is (= expected (family/observe f args)) (str [name engine n]))))))

(deftest growing-builders-and-retained-histories-remain-outside-owned-recipe
  (doseq [source ['(fn [n] (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc i)) acc)))
                  '(fn [n] (loop [i 0 acc [0] history []]
                             (if (< i n) (recur (inc i) (assoc acc 0 i) (conj history acc))
                               [acc history])))]]
    (is (= :unsupported-region
           (try (affine/infer (expand/expand-expr source world/empty-root)) nil
                (catch clojure.lang.ExceptionInfo e (:reason (ex-data e))))))))
