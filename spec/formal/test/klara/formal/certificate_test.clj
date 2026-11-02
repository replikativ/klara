(ns klara.formal.certificate-test
  "L4.check.certificate: a proof-carrying candidate, checked by the ansatz
  kernel against the actual (quoted) reference and candidate terms."
  (:require [clojure.test :refer [deftest is]]
            [klara.formal.certify]
            [klara.formal.laws]
            [klara.host.api :as k]))

(deftest L4-check-certificate
  (let [s (k/session {:roots ["lib" "spec/formal/cases"] :out (java.io.StringWriter.)})]
    (is (= [:rejected :L4.check.not-equivalent
            :ready [:long]
            41 :compiled
            :reference-semantics :reference
            :rejected :L4.check.certificate]
           (k/load-file s "spec/formal/cases/certified_identity.clj")))))

(deftest proof-search-in-a-job
  (let [s (k/session {:roots ["lib" "spec/formal/cases"] :out (java.io.StringWriter.)})]
    (is (= [:done :proved 3 7] (k/load-file s "spec/formal/cases/proof_search.clj")))))

(deftest proofs-where-they-pay   ; L4.check.certificate (showcase 3)
  (let [s (k/session {:roots ["lib" "spec/formal/cases"] :out (java.io.StringWriter.)})]
    (is (= [:rejected :L4.check.not-equivalent
            :ready [[:range -1048576 1048576]]
            3005007 :compiled
            :overflow :reference
            :rejected :L4.check.certificate]
           (k/load-file s "spec/formal/cases/certified_horner.clj")))))

(deftest composition-of-independent-rewrites   ; L4.check.law L4.check.certificate L4.check.premises
  (let [s (k/session {:roots ["lib" "spec/formal/cases"] :out (java.io.StringWriter.)})
        r (k/load-file s "spec/formal/cases/fused_horner.clj")]
    (is (= {:poly :ready :poly-evidence :ansatz
            :without-law :rejected :without-law-rule :L4.check.not-equivalent
            :score :ready :score-evidence :law
            :score-premises '[fused-horner/keep? fused-horner/poly fused-horner/score]
            :same true :score-path :compiled :poly-path :compiled
            :on-big true :on-big-outcome [:error :overflow]
            :on-list true :list-path :reference
            :after-change true :after-change-kind :interpreted
            :old-world-keeps true}
           r))))
