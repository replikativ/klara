(ns klara.examples-test
  "The acceptance programs under examples/ assert their own expectations;
  this runs each in a fresh session (design/00-model.md)."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(def programs
  ["worlds/main" "staging/power" "effects/jobs" "optimization/cube" "memory/retention"])

(deftest examples
  (doseq [p programs]
    (testing p
      (let [out (java.io.StringWriter.)
            s (k/session {:roots ["lib" "examples"] :out out})]
        (k/load-file s (str "examples/" p ".clj"))
        (is (str/includes? (str out) ": ok") (str out))))))
