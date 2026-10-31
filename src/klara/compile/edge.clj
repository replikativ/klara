(ns klara.compile.edge
  "Issuer-controlled checked edges within the pure guest preparation boundary.
   Creating an issuer is a trusted host extension, like checker registration.
   An opaque edge is not by itself a mathematical correctness proof."
  (:require [klara.core :as core]))

(def ^:private seal (Object.))
(deftype CheckedEdge [source target info authority])
(defmethod print-method CheckedEdge [_ out] (.write ^java.io.Writer out "#<checked-transformation>"))

(defn checked? [x]
  (and (instance? CheckedEdge x) (identical? seal (.-authority ^CheckedEdge x))))
(defn info [x]
  (when-not (checked? x) (throw (ex-info "unchecked transformation" {:reason :unchecked-edge})))
  (.-info ^CheckedEdge x))

(defn source [x] (info x) (.-source ^CheckedEdge x))
(defn target [x] (info x) (.-target ^CheckedEdge x))

(defn trusted-issuer
  "Privileged host adapter capability. Keep the returned function private and
   invoke it only after that adapter's semantic/structural checker succeeds.
   Source-backed guest strategies cannot call this API or return opaque edges."
  [rule contract evidence]
  (fn [source target details]
    (CheckedEdge. source target
      (assoc details :rule rule :contract contract :evidence evidence
                     :source-id (core/code-id source) :target-id (core/code-id target)) seal)))

(defn connects? [edge source target contract]
  (and (checked? edge)
       (= contract (:contract (info edge)))
       (= (core/code-id source) (:source-id (info edge)))
       (= (core/code-id target) (:target-id (info edge)))))

(defn chain-valid? [edges origin-id target-id contract]
  (and (vector? edges) (<= (count edges) 8)
       (loop [expected origin-id remaining edges]
         (if-let [accepted (first remaining)]
           (and (checked? accepted) (= contract (:contract (info accepted)))
                (= expected (:source-id (info accepted)))
                (recur (:target-id (info accepted)) (next remaining)))
           (= expected target-id)))))
