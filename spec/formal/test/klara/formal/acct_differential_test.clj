(ns klara.formal.acct-differential-test
  "Klara's accounts against the kernel-checked accounting calculus λ-acct
  (spec/formal/src/klara/formal/acct.clj): generated token programs, with
  aliases, multi-shot handlers, raises and catches, run through the real
  reader, expander and CEK machine and through λ-acct's step; the outcome,
  the wallet and the spent amount must agree."
  (:require [clojure.test :refer [deftest is]]
            [klara.formal.acct-bridge :as bridge]))

(def seeds (or (some-> (System/getenv "KLARA_DIFF_SEEDS") parse-long) 500))

(deftest generated-token-programs
  (let [results (map bridge/compare-seed (range seeds))
        outcomes (frequencies (map (comp :outcome :model) results))]
    (is (pos? (outcomes :L3.affine.reuse 0)) "reuse is exercised")
    (is (pos? (outcomes :uncaught 0)) "raises are exercised")
    (is (pos? (outcomes :unhandled 0)) "effects are exercised")
    (doseq [d (take 5 (remove :agree? results))]
      (is false (pr-str (select-keys d [:seed :form :model :impl]))))))
