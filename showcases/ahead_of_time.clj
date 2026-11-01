(ns showcases.ahead-of-time
  "Static when we want it.

  Run once with --record: the program runs interpreted and its profile is
  saved. Run again with --aot: each definition is compiled as soon as it is
  defined, from the saved profile, so the first call already runs compiled
  code. The rare refund is still handled: compiled code leaves for it and
  comes back.

    clojure -M:klara run --record /tmp/ledger.edn showcases/ahead_of_time.clj
    clojure -M:klara run --aot /tmp/ledger.edn showcases/ahead_of_time.clj"
  (:require [klara.effect :refer [perform handle]]
            [klara.compiler :as compiler]))

(defn fee [amount] (quot amount 100))

(defn settle [txs]
  (loop [i 0 balance 0]
    (if (< i (count txs))
      (let [amount (nth txs i)]
        (if (neg? amount)
          (recur (inc i) (+ balance (perform :review amount)))
          (recur (inc i) (+ balance (- amount (fee amount))))))
      balance)))

(def ledger (vec (for [i (range 400000)] (if (= i 300000) -500 (+ 100 (mod (* i 7919) 900))))))

(def t0 (System/nanoTime))
(def total (handle {:review (fn [k amount] (k amount))} (settle ledger)))
(def ms (/ (- (System/nanoTime) t0) 1000000.0))

(def report {:total total :first-run-ms ms :ran (or (:last-path (compiler/explain settle)) :interpreted)})
(println "total:" total "first run:" ms "ms, ran:" (:ran report))
report
