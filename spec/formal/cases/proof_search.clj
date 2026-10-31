(ns proof-search
  "Proof search as ordinary Klara code in a budgeted job: try proof scripts
  until the kernel accepts one. The result is data: it can be stored in a
  definition, forked and retained like any other value."
  (:require [klara.stage :refer [code]]
            [klara.job :as job]
            [klara.proof :as proof]
            [klara.compiler :as compiler]
            [certified-identity :as ci]))

(def reference (code (fn [x] (* x 1))))
(def candidate (code (fn [x] x)))

(def scripts ['[(rfl)] '[(omega)] ci/proof])

(defn search [ref cand scripts]
  (loop [ss scripts tried 0]
    (if (empty? ss)
      {:result :none :tried tried}
      (let [r (proof/certify ref cand (first ss))]
        (if (= :proved (:result r))
          (assoc r :tried (inc tried) :proof (first ss))
          (recur (rest ss) (inc tried)))))))

(def outcome (job/run {:budget {:steps 10000}} (fn [] (search reference candidate scripts))))

;; The found proof is a value; use it as the certificate.
(def theorem (:value outcome))
(def f (compiler/executable
         (compiler/prepare reference {:recipe (fn [_] candidate)
                                      :certificate {:kind :ansatz :proof (:proof theorem)}})))

[(:status outcome) (:result theorem) (:tried theorem) (f 7)]
