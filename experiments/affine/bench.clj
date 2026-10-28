(ns klara.affine-bench
  "Public JVM allocation counters; no Clojure implementation sources."
  (:refer-clojure :exclude [run!])
  (:require [klara.compile.core :as cc] [klara.defs :as d] [klara.world :as w])
  (:import [java.lang.management ManagementFactory]
           [com.sun.management ThreadMXBean]))

(def program
  '(defaffine counter [n]
     (let [o (own [0])]
       (loop [i 0]
         (if (< i n)
           (do (update! o (fn [v] (assoc v 0 (inc (nth v 0))))) (recur (inc i)))
           nil))
       (freeze o))))

(defn run! []
  (let [world (w/make-world)
        _ (d/define! world program)
        exe (cc/compile-def world 'counter)
        f (:run exe)
        ^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        tid (.threadId (Thread/currentThread))
        sample (fn [n]
                 (let [before (.getThreadAllocatedBytes bean tid)
                       result (f n)
                       after (.getThreadAllocatedBytes bean tid)]
                   (assert (= [n] result))
                   (- after before)))
        median (fn [xs] (nth (sort xs) (quot (count xs) 2)))]
    (assert (.isThreadAllocatedMemorySupported bean))
    (.setThreadAllocatedMemoryEnabled bean true)
    (dotimes [_ 300] (f 100000))
    (let [samples (into (sorted-map)
                       (for [n [0 1000 1000000]]
                         [n (vec (repeatedly 9 #(sample n)))]))
          medians (update-vals samples median)
          delta (- (medians 1000000) (medians 0))
          result {:java (System/getProperty "java.version")
                  :warmup {:calls 300 :iterations 100000}
                  :samples samples :median-bytes-per-call medians
                  :extra-bytes-for-million-iterations delta
                  :extra-bytes-from-1000-to-million (- (medians 1000000) (medians 1000))
                  :buffers (count (:representations exe))}]
      ;; A per-iteration object would add megabytes. Fixed call/entry/result
      ;; allocations remain; a zero slope is the claim, not a zero-byte call.
      (assert (<= delta 4096) (pr-str result))
      (prn result)
      result)))
