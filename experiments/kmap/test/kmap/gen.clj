(ns kmap.gen
  "Generators: nested Clojure trees with mixed numerics designed to collide
  across numeric types (1, 1N, 1.0, 1/2), nil, keywords, strings, records."
  (:require [clojure.test.check.generators :as gen]
            [kmap.core :as k]))

(defrecord R [a])

(def gen-long (gen/one-of [(gen/choose -3 3) gen/large-integer]))
(def gen-bigint (gen/fmap bigint gen-long))
(def gen-double (gen/one-of [(gen/fmap double (gen/choose -3 3))
                             (gen/elements [0.0 -0.0 0.5 -1.5 1e300])
                             (gen/double* {:NaN? false :infinite? true})]))
(def gen-ratio (gen/fmap (fn [[n d]] (/ n d))
                         (gen/tuple (gen/choose -7 7) (gen/elements [2 3 4]))))

(def gen-scalar
  (gen/frequency
   [[1 (gen/return nil)]
    [3 (gen/elements [:a :b :c :d :ns/a])]
    [2 (gen/elements ["" "a" "b" "abc"])]
    [3 gen-long]
    [2 gen-bigint]
    [2 gen-double]
    [2 gen-ratio]
    [1 (gen/elements [true false])]]))

(def gen-key
  (gen/frequency [[8 gen-scalar]
                  [1 (gen/fmap ->R gen-scalar)]]))

(defn- container [inner]
  (gen/frequency
   [[5 (gen/map gen-key inner {:max-elements 6})]
    [1 (gen/map (gen/map gen-key gen-scalar {:max-elements 2}) inner {:max-elements 3})]
    [2 (gen/vector inner 0 4)]
    [1 (gen/set inner {:max-elements 3})]
    [1 (gen/fmap ->R inner)]]))

(def gen-tree (gen/recursive-gen container gen-scalar))

(def gen-map
  "Top-level value is always a map."
  (gen/scale #(min % 40) (gen/map gen-key gen-tree {:max-elements 8})))

;; Numeric retyping: produces trees that are often `=` (1 ~ 1N) but
;; sometimes not (1 vs 1.0), so equality answers are non-trivial.
(defn retype [x choice]
  (cond
    (record? x) (->R (retype (:a x) choice))
    (map? x) (into (hash-map) (map (fn [[a b]] [(retype a choice) (retype b choice)])) x)
    (vector? x) (mapv #(retype % choice) x)
    (set? x) (into #{} (map #(retype % choice)) x)
    (instance? Long x) (case (long choice) 0 (bigint x) 1 (double x) 2 x x)
    (instance? clojure.lang.BigInt x) (case (long choice) 0 (long x) 1 x 2 (double x) x)
    :else x))

(defn mix-convert
  "Randomly (by a seed sequence) convert some nested maps to KMap."
  [x bits]
  (let [i (volatile! 0)
        pick (fn [] (let [b (nth bits (mod @i (count bits)))] (vswap! i inc) b))]
    ((fn walk [x]
       (cond
         (record? x) (->R (walk (:a x)))
         (map? x) (let [m (into (hash-map) (map (fn [[a b]] [(walk a) (walk b)])) x)]
                    (if (pick) (k/kmap m) m))
         (vector? x) (mapv walk x)
         (set? x) (into #{} (map walk) x)
         :else x))
     x)))

(def gen-case
  "[tree, retype-choice, conversion-bits]"
  (gen/tuple gen-map (gen/choose 0 3) (gen/vector gen/boolean 1 16)))
