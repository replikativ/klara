(ns klara.formal.certificate-test
  "L4.check.certificate: a proof-carrying candidate, checked by the ansatz
  kernel against the actual (quoted) reference and candidate terms."
  (:require [clojure.test :refer [deftest is]]
            [klara.formal.certify]
            [klara.host.api :as k]))

(deftest L4-check-certificate
  (let [s (k/session {:roots ["lib" "spec/formal/cases"] :out (java.io.StringWriter.)})]
    (is (= [:rejected :L4.check.not-equivalent
            :ready [:long]
            41 :compiled
            :reference-semantics :reference
            :rejected :L4.check.certificate]
           (k/load-file s "spec/formal/cases/certified_identity.clj")))))
