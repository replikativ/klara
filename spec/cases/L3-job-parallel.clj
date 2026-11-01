;; rules: L3.job.parallel
;; expect: [[:done :done :failed] [55 6765 nil] true true]
(ns jp (:require [klara.job :as job] [klara.world :as world]))
(defn fib [n] (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(def outer (atom 0))
(def outs (job/run-all {:budget {:steps 1000000}}
                       [(fn [] (fib 10)) (fn [] (fib 20)) (fn [] (swap! outer inc))]))
;; each job forked the world: a definition in one is not visible in another
(def worlds (job/run-all {} [(fn [] (def only-here 1) :a) (fn [] (world/generation (world/current) 'jp/only-here))]))
[(mapv :status outs) (mapv :value outs)
 (= :L3.job.host-mutation (get-in (nth outs 2) [:error :rule]))
 (nil? (:value (second worlds)))]
