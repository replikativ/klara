(ns klara.conformance-test
  "Runs spec/cases/*.clj through the full read, expand, load and evaluate
  path (spec/README.md#conformance). Each case declares
    ;; rules: L.. L..          the rules it exercises
    ;; expect: <edn>          the value of its last form, or
    ;; expect-rule: :L..      the :rule of the error it must raise"
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(defn- header [text key]
  (some->> (re-find (re-pattern (str "(?m)^;; " key ": (.*)$")) text) second str/trim))

(defn cases []
  (->> (file-seq (io/file "spec/cases"))
       (filter #(str/ends-with? (.getName ^java.io.File %) ".clj"))
       (sort-by #(.getName ^java.io.File %))))

(defn run-case
  "Returns {:value v} or {:rule r :message m}."
  [file]
  (let [s (k/session {:roots ["lib" "spec/cases"] :out (java.io.StringWriter.)})]
    (try {:value (k/eval-string s (slurp file))}
         (catch clojure.lang.ExceptionInfo e
           (let [d (ex-data e)] {:rule (:rule d) :message (.getMessage e)}))
         (catch Throwable e {:error (str e)}))))

(defn check-cases
  "Run every case and check it against its expectation."
  []
  (doseq [f (cases)]
    (let [text (slurp f)
          expect (header text "expect")
          expect-rule (header text "expect-rule")
          result (run-case f)]
      (testing (.getName ^java.io.File f)
        (if expect-rule
          (is (= (edn/read-string expect-rule) (:rule result)) (pr-str result))
          (is (= (edn/read-string expect) (:value result)) (pr-str result)))))))

(deftest conformance (check-cases))
