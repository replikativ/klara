(ns optimization.cube
  "Checked optimization: a generator as an optimizer, admitted only if equivalent."
  (:require [staging.power :refer [power power-gen]]
            [klara.stage :refer [code esc]]
            [klara.compiler :as compiler]))

;; The reference says what cube means. The recipe proposes how to compute it.
(def reference (code (fn [x] (power 3 x))))

(def outcome
  (compiler/prepare reference
    {:recipe (fn [_] (code (fn [x] (esc (power-gen 3 (code x))))))
     :budget {:steps 100000}}))

(assert (= :ready (:status outcome)))
(def cube (compiler/executable outcome))
(assert (= 27 (cube 3)))

;; The candidate relied on the current definition of power: that is its premise.
(assert (contains? (set (map first (:premises outcome))) 'staging.power/power))

;; A wrong recipe is rejected, with the rule that rejected it.
(def wrong (compiler/prepare reference {:recipe (fn [_] (code (fn [x] (* x x))))}))
(assert (= :rejected (:status wrong)))
(assert (= :L4.check.not-equivalent (:rule wrong)))

;; Algebra is not definitional: (* x 1) is not x, because x may not be a number.
(def clever (compiler/prepare reference
              {:recipe (fn [_] (code (fn [x] (* x (* x x)))))}))
(assert (= :rejected (:status clever)))

;; Too little budget is exhaustion, not rejection.
(def starved (compiler/prepare reference
               {:recipe (fn [_] (code (fn [x] (esc (power-gen 3 (code x))))))
                :budget {:steps 5}}))
(assert (= :exhausted (:status starved)))

;; The plain-function interface does the same for agents and casual use.
(def cube2 (compiler/specialize power {0 3}))
(assert (= 64 (cube2 4)))

;; Redefining power invalidates the premise; cube falls back to the reference.
(in-ns 'staging.power)
(defn power [n x] (if (= n 0) 1 (* x (power (dec n) x) 1)))   ; same values, new generation
(in-ns 'optimization.cube)
(assert (= 27 (cube 3)))
(assert (= :reference (:last-path (compiler/explain cube))))

(println "optimization: ok")
