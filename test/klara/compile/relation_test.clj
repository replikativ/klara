(ns klara.compile.relation-test
  (:require [clojure.test :refer [deftest is]] [klara.compile.core :as compiler]
            [klara.compile.core-test :refer [setup]] [klara.compile.local-calls :as local]
            [klara.compile.relation :as relation] [klara.core :as core] [klara.stage :as stage]))

(deftest exact-source-reconstruction-is-required-with-and-without-rewrites
  (let [w (setup '(fn [x] (let [helper (fn [y] (+ y 1))] (helper x))))
        _ (local/bootstrap! w)
        exe (compiler/compile-def w 'f {:mode :baseline :local-call-planner local/planner-symbol})
        wrong-source (core/lam 1 false (core/local 0))]
    (is (nil? (relation/check exe)))
    (is (= :relation-source (relation/check (assoc exe :code-id (core/code-id wrong-source)
                                                     :generic wrong-source))))
    (is (some? (relation/check (dissoc exe :rewrite-origin))))
    (is (= :relation-receipts (relation/check (assoc-in exe [:rewrite-receipts 0 :contract] :unchecked))))
    (is (some? (stage/check-certificate (assoc-in exe [:rewrite-origin :body] {:op :local :name 'escaped})))))
  (let [exe (compiler/compile-def (setup '(fn [x] (+ x 1))) 'f {:mode :baseline})]
    (is (nil? (relation/check exe)))
    (is (= :relation-source (relation/check (assoc exe :ir {:op :fn :arity 1 :rest? false
                                                          :params ['x] :body {:op :local :name 'x}}))))))
