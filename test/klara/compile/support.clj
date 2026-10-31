(ns klara.compile.support
  "Shared sources and world setup. Observations stay local to each obligation."
  (:require [klara.code :as code] [klara.expand :as expand]
            [klara.compile.local-calls :as local]
            [klara.defs :as defs] [klara.world :as world]))

(def source
  '(fn [n bias limit]
     (let [step (fn [acc i]
                  (assoc (assoc acc 0 (+ (nth acc 0) i))
                         1 (+ (nth acc 1) bias)))]
       (let [acc (loop [i 0 acc [0 0]]
                   (if (< i n) (recur (inc i) (step acc i)) acc))]
         (< (+ (nth acc 0) (nth acc 1)) limit)))))

(def strategy
  '(fn [r]
     (if (= (count (get r :history)) 0)
       {:action :local-call :planner 'klara.compiler/local-calls}
       {:action :private-accumulator})))

(defn setup [form]
  (let [w (world/make-world)]
    (local/bootstrap! w)
    (defs/define! w (list 'def 'strategy strategy))
    (defs/define! w (list 'def 'f form)) w))

(defn source-code [form]
  (code/->code (code/core->s (expand/expand-expr form world/empty-root))))
