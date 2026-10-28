(ns klara.compile.inline
  "Named core -> named core with known open world functions inlined.
  Obligation: every substituted definition has a value-id guard; cycles
  and captured closures remain unresolved. Fuel bounds code growth."
  (:require [klara.compile.ir :as ir] [klara.eval :as ev] [klara.world :as w]))

(defn run [term basis fuel]
  (let [guards (atom #{}) changes (atom 0)]
    (letfn [(go [t seen fuel]
              (if (and (= :resolve (:op t)) (pos? fuel) (not (seen (:id t))))
                (let [s (:id t) e (w/entry* basis s) v (:value e)]
                  (if (and (= :def (:kind e)) (not (w/pending? basis e))
                           (ev/closure? v) (empty? (ev/closure-locals v))
                           (nil? (ev/closure-basis v)))
                    (do (swap! guards conj [:world s (:value-id e)])
                        (swap! changes inc)
                        (go (ir/named (ev/closure-term v)) (conj seen s) (dec fuel))) t))
                (ir/map-children #(go % seen fuel) t)))]
      {:term (go term #{} fuel) :guards @guards :changes @changes})))
