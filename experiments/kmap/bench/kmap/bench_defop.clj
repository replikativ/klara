(ns kmap.bench-defop
  "defop :single vs Clojure protocol, mono / poly-3 / mega call sites.
  Run one (impl, scenario) per JVM so JIT profiles do not leak across."
  (:require [criterium.core :as crit]
            [kmap.core :as k]
            [kmap.defop :refer [defop defimpl]]))

(set! *warn-on-reflection* true)

(defprotocol PTag (ptag [x]))

(extend-protocol PTag
  kmap.core.KMap                    (ptag [_] 1)
  clojure.lang.PersistentHashMap    (ptag [_] 2)
  clojure.lang.PersistentArrayMap   (ptag [_] 3)
  clojure.lang.PersistentVector     (ptag [_] 4)
  clojure.lang.PersistentHashSet    (ptag [_] 5)
  String                            (ptag [_] 6)
  Long                              (ptag [_] 7)
  clojure.lang.Keyword              (ptag [_] 8))

(defop otag :single [x])
(defimpl otag kmap.core.KMap                  [_] 1)
(defimpl otag clojure.lang.PersistentHashMap  [_] 2)
(defimpl otag clojure.lang.PersistentArrayMap [_] 3)
(defimpl otag clojure.lang.PersistentVector   [_] 4)
(defimpl otag clojure.lang.PersistentHashSet  [_] 5)
(defimpl otag String                          [_] 6)
(defimpl otag Long                            [_] 7)
(defimpl otag clojure.lang.Keyword            [_] 8)

(def samples
  [(k/kmap {:a 1}) (apply hash-map (range 20)) {:a 1} [1 2] #{1} "s" 42 :kw])

(defn data ^objects [scenario]
  (let [n (case scenario "mono" 1 "poly2" 2 "poly3" 3 "mega" 8)
        rnd (java.util.Random. 7)]
    (object-array (repeatedly 1024 #(nth samples (.nextInt rnd n))))))

;; Each loop is its own fn so each has its own call site.
(defn loop-proto ^long [^objects xs]
  (let [n (alength xs)]
    (loop [i 0 acc 0]
      (if (< i n) (recur (inc i) (+ acc (long (ptag (aget xs i))))) acc))))

(defn loop-op ^long [^objects xs]
  (let [n (alength xs)]
    (loop [i 0 acc 0]
      (if (< i n) (recur (inc i) (+ acc (long (otag (aget xs i))))) acc))))

(defn -main [impl scenario out]
  (let [xs (data scenario)
        f (case impl "protocol" loop-proto "defop" loop-op)
        _ (assert (= (loop-proto xs) (loop-op xs)))
        r (crit/benchmark (f xs) {})
        ns-per-call (/ (* 1e9 (first (:mean r))) 1024)]
    (println (format "%-8s %-6s %7.3f ns/call (sd %.3f)" impl scenario ns-per-call
                     (/ (* 1e9 (Math/sqrt (first (:variance r)))) 1024)))
    (spit out (pr-str {:impl impl :scenario scenario :ns-per-call ns-per-call}) :append true)
    (spit out "\n" :append true)
    (shutdown-agents)))
