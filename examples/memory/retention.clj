(ns memory.retention
  "Lifetimes: what keeps memory alive is visible, and old versions are not kept by accident."
  (:require [klara.world :as world]
            [klara :as klara]))

(def dataset (vec (range 100000)))
(def setting 1)
(defn reader [] setting)

;; Pinning reader retains reader's footprint (reader, setting), not the whole world.
(def pinned (world/get (world/current) 'memory.retention/reader))
(assert (= #{'memory.retention/reader 'memory.retention/setting}
           (world/footprint pinned)))

;; Redefining dataset many times does not accumulate old datasets:
;; no root reaches them. (The JVM-level check is test/klara/lifetime_test.clj.)
(dotimes [i 20]
  (def dataset (vec (range 100000))))

(let [r (klara/retained)]
  (assert (<= (:history-entries r) (:history-limit r)))
  (println "retained:" (select-keys r [:world-definitions :history-entries :candidates :jobs])))

(println "retention: ok")
