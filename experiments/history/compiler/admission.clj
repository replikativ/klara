(ns klara.compile-admission
  "S17 public-API allocation/micro/JFR profile. No implementation sources."
  (:refer-clojure :exclude [run!])
  (:require [klara.compile-bench :as b] [klara.compile-profile :as p]
            [klara.compile.core :as cc] [klara.eval :as ev]
            [klara.stage :as s] [klara.world :as w] [klara.defs :as d]))

(defn run! []
  (let [recording (doto (jdk.jfr.Recording. (jdk.jfr.Configuration/getConfiguration "profile"))
                    (.start))
        world (w/make-world)
        _ (d/define! world '(def g (fn [x] (* x 2))))
        _ (d/define! world '(def f (fn [x] (g x))))
        root (w/snapshot world) f (d/lookup root 'f)
        cache (s/make-cache)
        _ (s/install! cache (cc/compile-def world 'g {:inline-fuel 0}))
        exe (cc/compile-def world 'f {:inline-fuel 0})
        _ (s/install! cache exe)
        select (s/make-entry-site cache) reads (atom #{})
        plus (fn [x] (+ x 2))
        functions [(fn [x] (+ x 2)) (fn [x] (+ x 2))
                   (fn [x] (+ x 2)) (fn [x] (+ x 2))]
        counter (volatile! 0)
        entries (:entries @cache) identity-slot [root entries]]
    (try
      (println {:java (System/getProperty "java.version") :clojure (clojure-version)
                :warmup 10000 :batches 9 :calls 10000 :units [:ns :bytes]})
      (s/with-cache cache
        (binding [ev/*basis* root ev/*mint* root]
          (doseq [[label call]
                  [[:driver #(identity 2)]
                   [:identity-checks #(and (identical? root (nth identity-slot 0))
                                          (identical? (:entries @cache) (nth identity-slot 1)))]
                   [:argument-vector #(vector 1000)]
                   [:boxed-arithmetic #(+ (identity 1000) (identity 2000))]
                   [:fixed-ifn #(plus 1000)]
                   [:apply-ifn #(apply plus [1000])]
                   [:polymorphic-ifn #((nth functions (bit-and (vswap! counter inc) 3)) 1000)]
                   [:binding #(binding [ev/*basis* root ev/*mint* root] 2)]
                   [:with-cache #(s/with-cache cache 2)]
                   [:read-disabled #(w/note-read! [:value 'g :probe])]
                   [:read-enabled #(binding [w/*reads* reads] (w/note-read! [:value 'g :probe]))]
                   [:handler-scan #(not-any? (fn [f] (= :dynamic (:mode f))) (mapcat identity ev/*outer-k*))]
                   [:selector #(select f [1] root)]
                   [:body #((:run exe) 1)]
                   [:invoke #(ev/invoke-direct exe f [1])]
                   [:entry #(f 1)]
                   [:entry-with-cache #(s/with-cache cache (f 1))]]]
            (println label (p/sample #(vreset! b/sink (call))))))
      (binding [w/*reads* reads]
        (println :read-recording-only (p/sample #(w/note-read! [:value 'g :probe])))))
      (when-let [invoke-context (ns-resolve 'klara.eval 'invoke-context)]
        (s/with-cache cache
          (binding [ev/*basis* root ev/*mint* root]
            (let [ctx ((ns-resolve 'klara.stage 'current-context))]
              (println :explicit-invoke (p/sample #(invoke-context ctx exe f 1)))))))
      (d/define! world (list 'def 'call-loop (:calls b/programs)))
      (let [loop-exe (cc/compile-def world 'call-loop {:inline-fuel 0})
            loop-f (d/lookup (w/snapshot world) 'call-loop)]
        (s/install! cache loop-exe)
        (s/with-cache cache
          (assert (= 40200 (loop-f 200)))
          (println :call-loop-200 (p/sample #(vreset! b/sink (loop-f 200))))))
      (finally
        (.stop recording)
        (.dump recording (java.nio.file.Path/of "/tmp/klara-s17.jfr" (make-array String 0)))
        (.close recording)))))
