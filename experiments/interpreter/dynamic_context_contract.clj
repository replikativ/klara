;; Bounded counterexample: private-buffer independence is not complete
;; deterministic snapshot semantics when host dynamic context changes.
;; Run: clojure -M experiments/interpreter/dynamic_context_contract.clj
(require '[klara.expand :as x] '[klara.world :as w])
(load-file "experiments/interpreter/mutable.clj")

(let [f (interpreter.mutable/prepare
          (x/expand-expr '(fn [] (/ 1M 3M)) w/empty-root))
      frozen (interpreter.mutable/freeze (interpreter.mutable/start f []))
      p3 (binding [*math-context* (java.math.MathContext. 3)]
           (interpreter.mutable/run! (interpreter.mutable/thaw frozen)))
      p6 (binding [*math-context* (java.math.MathContext. 6)]
           (interpreter.mutable/run! (interpreter.mutable/thaw frozen)))]
  (assert (= 0.333M p3))
  (assert (= 0.333333M p6))
  (prn {:probe :snapshot-host-math-context :precision-3 p3 :precision-6 p6}))
