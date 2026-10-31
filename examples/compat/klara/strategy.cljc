(ns klara.strategy
  (:require [klara.local-optimizer] [klara.compiler]))

;; Generate a pure strategy now. The controller passes inert history and fresh
;; shape facts; it retains source, checked edges, roots and funding privately.
(defn strategy-code [rewrites]
  (code
    (fn [request]
      (let [history (get request :history)]
        (if (= (count history) 0)
          {:action :inspect}
          (if (< (count history) (esc (lift (inc rewrites))))
            (if (> (get (get request :source) :local-functions) 0)
              {:action :local-call :planner 'klara.local-optimizer/planner}
              {:action :finish})
            {:action :finish}))))))

(def strategy (run (strategy-code 2)))

(defn subject [source] (perform :stage/subject source))

(defn prepare [job subject]
  (klara.compiler/prepare-request subject
    {:job job :strategy 'klara.strategy/strategy
     :backend :baseline :strategy-steps 4}))
