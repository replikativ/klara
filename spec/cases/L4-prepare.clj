;; rules: L4.prepare.job L4.check.delta L4.check.beta L4.check.if-constant L4.check.prim L4.check.premises L4.exec.executable L4.exec.valid L4.lower.links
;; expect: [:ready 8 [k1/power] :compiled]
(ns k1 (:require [klara.stage :refer [code esc]] [klara.compiler :as compiler]))
(defn power [n x] (if (= n 0) 1 (* x (power (dec n) x))))
(defn gen [n x] (if (= n 0) (code 1) (code (* (esc x) (esc (gen (dec n) x))))))
(def o (compiler/prepare (code (fn [x] (power 3 x))) {:recipe (fn [_] (code (fn [x] (esc (gen 3 (code x))))))}))
(def cube (compiler/executable o))
[(:status o) (cube 2) (mapv first (:premises o)) (:last-path (compiler/explain cube))]
