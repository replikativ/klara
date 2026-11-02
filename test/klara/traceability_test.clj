(ns klara.traceability-test
  "Every specified rule is exercised, and every rule the implementation
  raises is specified (spec/README.md#rule-ids)."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]))

(def rule-id #"L[0-4]\.[a-z]+(?:-[a-z]+)*\.[a-z]+(?:[-?][a-z]+)*")

(defn- files [dir ext]
  (->> (file-seq (io/file dir)) (filter #(str/ends-with? (.getName ^java.io.File %) ext))))

(defn- ids-in [fs] (into #{} (mapcat #(re-seq rule-id (slurp %))) fs))

(defn specified
  "Rule IDs defined in spec/*.md, split by whether they are marked planned."
  []
  (let [text (str/join "\n" (map slurp (files "spec" ".md")))
        defs (re-seq #"(?m)^`(L[0-4][^`]+)`( \(planned\))?" text)]
    {:all (set (map second defs))
     :planned (set (map second (filter #(nth % 2) defs)))}))

(def structural
  "Rules that define representations rather than behaviour; they are
   exercised by every test rather than by a dedicated one."
  #{"L0.value.data" "L0.value.other" "L0.term.free" "L1.retain.roots" "L2.code.value"
    "L2.view.make"})

(deftest every-implemented-rule-is-tested
  (let [{:keys [all planned]} (specified)
        cited (ids-in (concat (files "test" ".clj") (files "spec/cases" ".clj") (files "spec/formal" ".clj")))
        missing (set/difference all planned structural cited)]
    (is (empty? missing) (str "rules without a test or case: " (sort missing)))))

(deftest every-raised-rule-is-specified
  (let [{:keys [all]} (specified)
        raised (into #{} (map #(subs % 1))
                     (mapcat #(re-seq #":L[0-4]\.[a-z-]+\.[a-z-?]+" (slurp %))
                             (concat (files "src" ".clj") (files "lib" ".clj"))))
        unknown (set/difference raised all)]
    (is (empty? unknown) (str "rules raised but not specified: " (sort unknown)))))

(deftest every-cited-rule-is-specified
  (let [{:keys [all]} (specified)
        docs (concat (files "design" ".md") (map io/file ["README.md" "STATUS.md" "AGENTS.md"]))
        cited (ids-in (concat (files "src" ".clj") (files "lib" ".clj") (files "test" ".clj")
                              (files "spec/cases" ".clj") (files "showcases" ".clj") docs))
        unknown (set/difference cited all)]
    (is (empty? unknown) (str "rules cited but not specified: " (sort unknown)))))

