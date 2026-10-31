(ns interpreter.staged-baseline-review
  "Untimed design probe. Direct emitter checks are not installed candidates
   and establish neither admission correctness nor a preparation speedup."
  (:require [klara.world :as w] [klara.defs :as d] [klara.stage :as stage]
            [klara.compile.core :as cc] [klara.compile.loop :as transfer]
            [klara.compile.ir :as ir] [klara.compile.emit :as emit]
            [klara.expand :as x] [klara.eval :as ev]))

(def transfer-source
  '(fn [destinations arguments]
     (loop [i 0 evaluations [] commits []]
       (if (< i (count arguments))
         (recur (inc i)
                (conj evaluations {:temporary i :expression (nth arguments i)})
                (conj commits {:destination (nth destinations i) :temporary i}))
         {:evaluations evaluations :commits commits}))))

(defn probe []
  (let [world (w/make-world)
        _ (d/define! world (list 'def 'guest-transfer transfer-source))
        exe (cc/compile-def world 'guest-transfer {:fuel 0 :inline-fuel 0})
        cache (stage/make-cache)
        arguments [{:op :local :name 'b} {:op :local :name 'a}]
        destinations ['a 'b]
        form (list 'guest-transfer (list 'quote destinations) (list 'quote arguments))
        _ (stage/install! cache exe)
        results (mapv (fn [_]
                        (let [v (stage/with-cache cache (d/eval-form (w/snapshot world) form))]
                          {:value v :deopts (:deopts (stage/stats cache))})) (range 5))
        source (ev/closure-term (:value (w/entry* (w/snapshot world) 'guest-transfer)))
        bare (emit/run (ir/lower (ir/named source)))
        expected (transfer/transfer destinations arguments)]
    (assert (every? #(= expected (:value %)) results))
    (assert (= expected ((:run bare) destinations arguments)))
    (transfer/check-transfer! destinations arguments (:value (first results)))
    (doseq [program ['(fn [x] (let [y (+ x 1)] (if (< y 0) (- y) (* y y))))
                     '(fn [n] (loop [i 0 a 1 b 2]
                                (if (< i n) (recur (inc i) b (+ a b)) a)))]]
      (let [term (x/expand-expr program w/empty-root)
            emitted (emit/run (ir/lower (ir/named term))) f (ev/run term)]
        (doseq [n [-2 0 1 2 5]]
          (assert (= (ev/call-value f [n]) ((:run emitted) n))))))
    {:transfer-plan :agrees-and-checked
     :mandatory-only-emission :agrees-on-selected-inputs
     :stock-compiler-deopts (mapv :deopts results)
     :stock-compiler-passes (:pass-log exe)
     :declines
     (mapv
       (fn [[label program]]
         (d/define! world (list 'def 'bad program))
         (let [reason (try (cc/compile-def world 'bad {:fuel 0 :inline-fuel 0})
                           :unexpected-accepted
                           (catch clojure.lang.ExceptionInfo e (:reason (ex-data e))))]
           (assert (not= :unexpected-accepted reason))
           {:case label :reason reason}))
       [[:stage '(fn [x] (code (+ (esc x) 1)))]
        [:world-recursion '(fn [x] (if (> x 0) (bad (dec x)) 0))]
        [:keyword-call '(fn [x] (:op x))]])}))

(defn -main [& _] (prn (probe)))
