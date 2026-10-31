(ns klara.compile.funding
  "Explicit operational preparation allowance, shared across requests/forks.
   Counters are intentionally not rolled back with application worlds."
  (:require [klara.compile.budget :as budget]))

(deftype Funding [counter])
(defmethod print-method Funding [_ out] (.write ^java.io.Writer out "#<preparation-funding>"))
(defn funding? [x] (instance? Funding x))
(defn create [limits]
  (budget/validate-limits! limits budget/units)
  (when (some (fn [[k v]] (> v (get budget/session-limits k))) limits)
    (throw (ex-info "guest preparation allowance exceeds session cap" {:reason :invalid-budget})))
  (Funding. (budget/budget (merge budget/session-limits limits))))
(defn counter [^Funding f] (.-counter f))
(defn usage [^Funding f] (budget/usage (counter f)))
