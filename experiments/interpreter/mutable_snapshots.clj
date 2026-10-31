(ns interpreter.mutable-snapshots
  (:require [interpreter.mutable :as m] [interpreter.mutable-checks :as checks]
            [interpreter.run :as driver] [clojure.pprint :as pp] [clojure.java.io :as io]
            [klara.core :as core] [klara.expand :as x] [klara.world :as w])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]))

(let [term (x/expand-expr (second checks/programs) w/empty-root)
      f (m/prepare term) state (m/start f [16]) _ (m/advance! state 200)
      expected (m/run! (m/thaw (m/freeze state)))
      bean ^ThreadMXBean (ManagementFactory/getThreadMXBean)
      _ (.setThreadAllocatedMemoryEnabled bean true)
      tid (.threadId (Thread/currentThread)) sink (volatile! nil)
      operation #(m/thaw (m/freeze state))
      _ (dotimes [_ 100] (vreset! sink (operation)))
      samples (mapv (fn [_]
                      (let [before (.getThreadAllocatedBytes bean tid) t (System/nanoTime)]
                        (dotimes [_ 100] (vreset! sink (operation)))
                        {:ns-per-pair (/ (- (System/nanoTime) t) 100.0)
                         :bytes-per-pair (/ (- (.getThreadAllocatedBytes bean tid) before) 100.0)}))
                    (range 9))
      result {:java (System/getProperty "java.runtime.version") :scope :freeze-and-thaw-only
              :workload :fib-16 :paused-after-transitions 200 :expected expected
              :median-ns (driver/median (map :ns-per-pair samples))
              :median-bytes (driver/median (map :bytes-per-pair samples)) :samples samples
              :source-sha256 (into {} (for [p ["deps.edn" "experiments/interpreter/mutable.clj"
                                              "experiments/interpreter/mutable_snapshots.clj"
                                              "experiments/interpreter/mutable_checks.clj"]]
                                       [p (core/sha256 (slurp p))]))
              :limits [:one-state :one-process :not-constant-time :not-durable :no-authority]}]
  (assert (= expected (m/run! @sink) (m/run! (m/thaw (m/freeze state)))))
  (io/make-parents "target/interpreter/mutable-snapshots.edn")
  (spit "target/interpreter/mutable-snapshots.edn" (with-out-str (pp/pprint result)))
  (println (select-keys result [:workload :median-ns :median-bytes :expected])))
