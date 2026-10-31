(ns consolidation.enclosed-consumer-test
  (:require [clojure.test :refer [deftest is]] [ansatz.core :as a]
            [consolidation.enclosed-consumer :as model] [consolidation.private-state :as private]
            [klara.compile.support :as fixture] [klara.compile.private-accumulator] [klara.compile.edge :as edge]
            [klara.compile.funding :as funding] [klara.compile.analysis :as analysis]
            [klara.compile.infer-affine :as inference] [klara.compile.staged :as staged]
            [klara.defs :as defs] [klara.eval :as ev] [klara.stage :as stage] [klara.world :as world]))

(deftest private-simulation-lifts-through-an-enclosed-consumer
  (let [before @a/ansatz-env receipts (model/verify-theorems!)]
    (is (identical? before @a/ansatz-env))
    (is (= 4 (count receipts)))
    (doseq [r receipts] (is (:kernel-accepted r)) (is (false? (:self-reference r))))))

(defn observe [thunk]
  (try [:value (thunk)]
       (catch Throwable e
         (if (some #(instance? ArithmeticException %) (take-while some? (iterate ex-cause e)))
           [:error :overflow] (throw e)))))

(deftest finite-model-to-source-residual-owned-and-JVM-bridge
  ;; These checks exercise extraction and representation correspondence.
  ;; They do not make the Core/JVM bridge a kernel theorem.
  (doseq [seed [0 2 (dec Long/MAX_VALUE) Long/MAX_VALUE]
          checked-consumer? [false true]]
    (let [form (list 'fn '[n limit]
                    (list 'let ['step '(fn [acc] (assoc acc 0 (inc (nth acc 0))))]
                          (list 'let ['acc (list 'loop ['i 0 'acc [seed]]
                                                '(if (< i n) (recur (inc i) (step acc)) acc))]
                                (if checked-consumer? '(< (inc (nth acc 0)) limit) '(< (nth acc 0) limit)))))
          w (fixture/setup form) root (world/snapshot w)
          source (defs/eval-form root (list 'code form))
          r (staged/request root source {:job (funding/create {}) :strategy 'strategy})
          p (:candidate r) exe (.-executable ^klara.compile.staged.Prepared p)
          endpoint (:private-endpoint exe)
          residual (ev/run (analysis/indexed (edge/source (peek (:checked-edges exe)))) {:basis root})
          owned {:owned (.-owned ^klara.compile.private_accumulator.Endpoint endpoint)
                 :derivation (.-derivation ^klara.compile.private_accumulator.Endpoint endpoint)}
          f (defs/lookup root 'f) cache (stage/make-cache)]
      (is (= :installed (:status (staged/install! cache root (staged/prevalidate p)))))
      (doseq [n [0 1 2 5] limit [0 3 Long/MAX_VALUE]]
        (let [plan (nth (iterate #(vector :bump %) :done) n)
              reference (private/run-source plan seed [] [41] Long/MAX_VALUE)
              expected (if (:error reference) [:error :overflow]
                         (observe #(< (if checked-consumer? (inc (:value reference)) (:value reference)) limit)))
              call #(binding [ev/*basis* root ev/*mint* root] (ev/call-value % [n limit]))]
          (is (= expected (observe #(stage/with-cache (stage/make-cache) (call f)))
                         (observe #(call residual))
                         (observe #(inference/execute-owned owned [n limit]))
                         (observe #(stage/with-cache cache (call f)))))))
      (is (pos? (:hits (stage/stats cache)))))))
