(ns baseline.staged-composition-test
  (:require [clojure.test :refer [deftest is]]
            [baseline.staged-composition :as composition]
            [klara.compile.budget :as budget] [klara.compile.ir :as ir]
            [klara.expand :as expand] [klara.world :as world]))

(deftest two-rounds-expose-helper-calls-then-guarded-layouts
  (let [r (composition/run-example) [a b c] (:facts r)]
    (is (= [1 1] (:calls-inlined r)))
    (is (every? empty? (map :kinds (:loops a))))
    (is (every? empty? (map :kinds (:loops b))))
    (is (= [[:long :double]] (mapv :kinds (:loops c))))
    (is (= :runtime-class-guards (:entry-requires c)))
    (is (= :stale-analysis (get-in r [:stale-fact-rejection :reason])))
    (is (not= (:original-code-id r) (:residual-code-id r)))
    (is (pos? (get-in r [:native-entry-stats :hits])))
    (is (zero? (get-in r [:native-entry-stats :fallbacks])))))

(deftest identity-is-necessary-but-not-sufficient-for-facts
  (let [term (ir/named (expand/expand-expr composition/source world/empty-root))
        b (budget/budget) facts (composition/layout-facts b term)]
    (is (= facts (composition/validate-facts! b term facts)))
    (is (= :invalid-analysis
           (try (composition/validate-facts! b term (assoc-in facts [:loops 0 :kinds] [:long])) nil
                (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))))
