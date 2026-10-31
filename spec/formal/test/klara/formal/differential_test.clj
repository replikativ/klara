(ns klara.formal.differential-test
  "The CEK machine against the kernel-checked semantics (spec/formal).
  Generated programs and the conformance corpus go through the real reader
  and expander; every form inside the formal fragment must produce the same
  observation in both."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [klara.formal.bridge :as bridge]
            [klara.formal.gen :as gen]))

(def seeds (or (some-> (System/getenv "KLARA_DIFF_SEEDS") parse-long) 500))

(defn- disagreements [results]
  (for [r results :when (and (contains? r :agree?) (not (:agree? r)))] r))

(deftest generated-programs
  (let [results (mapcat #(bridge/compare-source (gen/program %)) (range seeds))
        compared (filter #(contains? % :agree?) results)]
    (is (> (count compared) seeds) "most generated forms are inside the fragment")
    (doseq [d (take 5 (disagreements results))]
      (is false (pr-str (select-keys d [:form :impl :model]))))))

(deftest conformance-corpus
  (doseq [f (->> (file-seq (io/file "spec/cases")) (filter #(.endsWith (.getName ^java.io.File %) ".clj")))]
    (testing (.getName ^java.io.File f)
      (doseq [d (disagreements (bridge/compare-source (slurp f) :roots ["lib" "spec/cases"]))]
        (is false (pr-str (select-keys d [:form :impl :model])))))))
