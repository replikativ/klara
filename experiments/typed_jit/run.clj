;; Run with (load-file "experiments/typed_jit/run.clj") in a persistent
;; Clojure REPL started at the repository root. No benchmark JVM is restarted.
(load-file "experiments/typed_jit/emit.clj")

(require '[klara.world :as world] '[klara.defs :as defs]
         '[klara.compile.core :as compiler] '[klara.stage :as stage])

(let [out (doto (java.io.File. "/tmp/klara-s20-classes") .mkdirs)
      javac (javax.tools.ToolProvider/getSystemJavaCompiler)
      sources ["experiments/typed_jit/Context.java"
               "experiments/typed_jit/generated/F2.java"
               "experiments/typed_jit/generated/F3.java"
               "experiments/typed_jit/Probe.java"
               "experiments/compiler/java/klara/bench/Baselines.java"]
      args (into-array String (concat ["-d" (.getPath out)] sources))]
  (assert (zero? (.run javac nil System/out System/err args)))
  (with-open [loader (java.net.URLClassLoader.
                      (into-array java.net.URL [(.toURL (.toURI out))])
                      (.getContextClassLoader (Thread/currentThread)))]
    (let [probe (Class/forName "klara.typedprobe.Probe" true loader)]
      (.invoke (.getMethod probe "run" (make-array Class 0))
               nil (object-array 0)))))

(let [w (world/make-world)
      _ (defs/define! w '(def g (fn [x] (* x 2))))
      _ (defs/define! w '(def f (fn [n]
                               (loop [i n s 0]
                                 (if (> i 0)
                                   (recur (dec i) (+ s (g i))) s)))))
      cache (stage/make-cache)
      _ (stage/install! cache (compiler/compile-def w 'g {:inline-fuel 0}))
      _ (stage/install! cache (compiler/compile-def w 'f {:inline-fuel 0}))
      f (defs/lookup (world/snapshot w) 'f)
      bean (cast com.sun.management.ThreadMXBean
                 (java.lang.management.ManagementFactory/getThreadMXBean))
      thread-id (.threadId (Thread/currentThread))
      sink (volatile! nil)
      median (fn [xs] (nth (sort xs) 4))
      sample (fn [n]
               (let [call #(vreset! sink (f n))]
                 (dotimes [_ 10000] (call))
                 (let [pairs (doall
                              (for [_ (range 9)]
                                (let [before-bytes (.getThreadAllocatedBytes bean thread-id)
                                      start (System/nanoTime)]
                                  (dotimes [_ 10000] (call))
                                  [(quot (- (System/nanoTime) start) 10000)
                                   (quot (- (.getThreadAllocatedBytes bean thread-id)
                                            before-bytes) 10000)])))]
                   {:ns (median (map first pairs))
                    :bytes (median (map second pairs))})))]
  (stage/with-cache cache
    (doseq [n [200 2000]]
      (assert (= (* n (inc n)) (f n)))
      (println (str "n=" n " klara-compiled " (pr-str (sample n)))))))
