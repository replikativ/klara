(ns klara.compile.scheduling-test
  (:require [clojure.test :refer [deftest is]]
            [klara.compile.prepare :as prepare] [klara.compile.budget :as budget]
            [klara.defs :as defs] [klara.stage :as stage] [klara.world :as world]))

(deftest explicit-threshold-shares-preparation-and-spend
  (let [w (world/make-world) _ (defs/define! w '(def f (fn [x] (+ x 1))))
        root (world/snapshot w) job (prepare/job) cache (stage/make-cache)
        request {:name 'f :file :interactive}
        controller (prepare/sponsor job {:mode :threshold :threshold 3})]
    (is (= :waiting (:status (prepare/checkpoint! controller root request cache 2))))
    (is (= {} (budget/usage (:budget job))))
    (is (= :complete (:status (prepare/checkpoint! controller root request cache 1))))
    (let [spent (budget/usage (:budget job))]
      (is (pos? (:emissions spent)))
      (is (= :already-attempted (:reason (prepare/checkpoint! controller root request cache 100))))
      (is (= spent (budget/usage (:budget job))))
    (defs/define! w '(def f (fn [x] (+ x 2))))
    (is (= :waiting (:status (prepare/checkpoint! controller (world/snapshot w) request cache 1))))
    (is (= :interpret (:reason (prepare/checkpoint! (prepare/sponsor job {:mode :interpret}) root request cache 100))))
    (is (thrown? clojure.lang.ExceptionInfo (prepare/sponsor job {:mode :threshold :threshold 0}))))))

(deftest fixed-before-use-declines-once-without-refund
  (let [w (world/make-world) _ (defs/define! w '(def f (fn [g] (g 1))))
        root (world/snapshot w) job (prepare/job) controller (prepare/sponsor job {})
        request {:name 'f :file :unsupported} cache (stage/make-cache)]
    (is (= :declined (get-in (prepare/checkpoint! controller root request cache 0) [:definitions 0 :status])))
    (let [spent (budget/usage (:budget job))]
      (is (pos? (:work spent)))
      (is (= :already-attempted (:reason (prepare/checkpoint! controller root request cache 1))))
      (is (= spent (budget/usage (:budget job)))))))
