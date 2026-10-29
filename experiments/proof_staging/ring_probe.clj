;; Reproduction for ansatz at 5a7f01a, observed in a local/root JVM.
;; Expected: a kernel-checkable polynomial identity certificate, or a clean
;; unsupported-tactic failure. Actual: ClassCastException in poly-normalize111.
;; Even after that bug, ring.clj currently has no non-ground proof producer.
(require '[ansatz.core :as a])
(a/init!)
(a/theorem KlaraExperiment.ring-probe
  [a :- Nat, b :- Nat, c :- Nat, x :- Nat]
  (= Nat (+ a (+ (* x b) (* (* x x) c)))
         (+ a (* x (+ b (* x c)))))
  (ring))
