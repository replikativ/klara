(ns klara.compile-profile
  "ThreadMXBean allocation measurements; public JVM API, no source inspection."
  (:refer-clojure :exclude [run!])
  (:require [klara.compile-bench :as b] [klara.compile.core :as cc]
            [klara.defs :as d] [klara.world :as w] [klara.eval :as ev]
            [klara.stage :as s]))

(defn sample [f]
  (dotimes [_ 10000] (f))
  (let [^com.sun.management.ThreadMXBean bean (java.lang.management.ManagementFactory/getThreadMXBean)
        id (.threadId (Thread/currentThread))
        batches (repeatedly 9
                  #(let [a (.getThreadAllocatedBytes bean id) t (System/nanoTime)]
                     (dotimes [_ 10000] (f))
                     {:ns (/ (- (System/nanoTime) t) 10000.0)
                      :bytes (/ (- (.getThreadAllocatedBytes bean id) a) 10000.0)}))
        results (vec batches)]
    (into {} (for [k [:ns :bytes]] [k (b/median (map k results))]))))

(defn run! []
  (println {:java (System/getProperty "java.version") :clojure (clojure-version)
            :warmup 10000 :batches 9 :calls 10000})
  (doseq [n [0 200 2000]]
    (let [world (w/make-world) _ (d/define! world (list 'def 'f (:numeric b/programs)))
          f (:value (w/entry* (w/snapshot world) 'f)) exe (cc/compile-def world 'f)
          emitted (eval (:form exe)) cache (s/make-cache)
          _ (s/install! cache exe) root (w/snapshot world)]
      (println {:input n :form (:form exe)})
      (doseq [[label call] [[:plain #((:numeric b/clojure-functions) n)]
                           [:emitted #(emitted n)] [:wrapper #((:run exe) n)]
                           [:entry #(s/enter cache f [] [n] root [])]
                           [:compiled #(s/with-cache cache (ev/call-value f [n]))]]]
        (println label (sample call))))))
