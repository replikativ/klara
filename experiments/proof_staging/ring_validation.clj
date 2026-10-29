(ns ring-validation
  "Independent consumer checks for the isolated ansatz symbolic ring revision.
   Run with a local/root override; does not change Klara's dependency pin."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as nm]
            [clojure.test :as test :refer [deftest is]]
            [klara.fusion.kernel :as k]))

(defn- changed-right-side [goal]
  (if (e/forall? goal)
    (e/forall' (e/forall-name goal) (e/forall-type goal)
               (changed-right-side (e/forall-body goal)) :default)
    (let [[eq [type lhs rhs]] (e/get-app-fn-args goal)]
      (e/app* eq type lhs (e/app* (k/c "Nat.add") rhs (e/lit-nat 1))))))

(deftest exact-horner-and-independent-kernel-recheck
  ;; Load the unmodified original reproduction, including its precise theorem.
  (load-file "experiments/proof_staging/ring_probe.clj")
  (let [en (a/env)
        declaration (env/lookup en (nm/from-string "KlaraExperiment.ring-probe"))
        goal (env/ci-type declaration)
        proof (env/ci-value declaration)
        constants (k/constants-of proof)
        accepts? (env/verifies? en goal proof)
        rejects? (not (env/verifies? en (changed-right-side goal) proof))]
    (is (some? proof))
    (is (contains? constants "Lean.Grind.CommRing.eq_normS"))
    (is (not (contains? constants "KlaraExperiment.ring-probe")))
    (is accepts? "strict kernel recheck of the extracted closed proof")
    (is rejects? "same proof cannot license a right-hand side increased by one")
    (println :ring-proof {:declarations (.size ^ansatz.kernel.Env en)
                          :kernel-accepted accepts?
                          :changed-endpoint-rejected rejects?
                          :goal-sha256 (k/expr-hash goal)
                          :proof-sha256 (k/expr-hash proof)})
    (let [result (try
                   (a/theorem KlaraExperiment.ring-false
                     [a :- Nat, b :- Nat, c :- Nat, x :- Nat]
                     (= Nat (+ a (+ (* x b) (* (* x x) c)))
                            (+ (+ a (* x (+ b (* x c)))) 1))
                     (ring))
                   {:status :unexpected-success}
                   (catch clojure.lang.ExceptionInfo ex
                     {:status :rejected :kind (:kind (ex-data ex))
                      :message (.getMessage ex)}))]
      (is (= :rejected (:status result)))
      (is (= :tactic-error (:kind result)))
      (is (re-find #"polynomial normalization could not certify" (:message result)))
      (is (identical? en (a/env)) "failed theorem leaves the environment unchanged")
      (is (nil? (env/lookup (a/env) (nm/from-string "KlaraExperiment.ring-false"))))
      (println :false-ring-identity result))))

(defn -main [& _]
  (let [ring-result (test/run-tests 'ring-validation)]
    (require 'proof-staging-test)
    (let [staging-result (test/run-tests 'proof-staging-test)]
      (System/exit (+ (:fail ring-result) (:error ring-result)
                      (:fail staging-result) (:error staging-result))))))
