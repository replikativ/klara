(ns consolidation.loop-review
  "Untimed compiler-review probe of the existing staged scalar loop path.
   No new compiler, proof or performance claim. Run with:
   clojure -Sdeps '{:paths [\"src\" \"experiments\"]}' -M -m consolidation.loop-review"
  (:require [klara.defs :as d] [klara.world :as w]
            [klara.code :as code] [klara.compile.ir :as ir]
            [klara.compile.scalar :as scalar] [klara.compile.staged :as sc]
            [klara.stage :as stage] [klara.eval :as ev]))

(def cases
  [[:three-parameters
    '(fn [n] (loop [i 0 a 1 b 2]
               (if (< i n) (recur (+ i 1) b (+ a b)) a)))
    [0 1 2 5 12]]
   [:stride-and-early-exit
    '(fn [n] (loop [i 0 a 1 b 2]
               (if (< i n)
                 (if (> a 20) b (recur (+ i 2) b (+ a b)))
                 a)))
    [0 1 2 5 12 100]]])

(defn probe [[label form inputs]]
  (let [source (d/eval-form w/empty-root (list 'code form))
        core (code/s->core (code/code-term source))
        named (ir/named core)
        typed (scalar/analyze (:body named)
                              (zipmap (:params named) (repeat :long)) {} nil)
        candidate (sc/prepare w/empty-root source)
        cache (stage/make-cache)
        closure (ev/run core)]
    (assert (= :installed (:status (sc/install! cache w/empty-root candidate))))
    (let [values (mapv (fn [n]
                         (let [reference (ev/call-value closure [n])
                               compiled (stage/with-cache cache (ev/call-value closure [n]))]
                           (assert (= reference compiled))
                           [n reference compiled])) inputs)
          stats (stage/stats cache)]
      (assert (= (count inputs) (:hits stats)))
      {:case label
       :loops (mapv #(select-keys % [:op :invariant])
                    (filter #(= :loop (:op %)) (tree-seq coll? seq typed)))
       :values values
       :stage-stats stats})))

(defn -main [& _]
  (doseq [test-case cases] (prn (probe test-case))))
