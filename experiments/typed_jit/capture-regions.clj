(load-file "experiments/typed_jit/run-regions.clj")
(let [r (jdk.jfr.Recording. (jdk.jfr.Configuration/getConfiguration "profile"))]
  (try
    (doseq [event ["jdk.Compilation" "jdk.CompilerInlining" "jdk.Deoptimization"]]
      (.withThreshold (.enable r event) java.time.Duration/ZERO))
    (.start r)
    (region-bench!)
    (finally
      (.stop r)
      (.dump r (java.nio.file.Path/of "/tmp/klara-s21-regions.jfr" (make-array String 0)))
      (.close r))))
(load-file "experiments/typed_jit/summarize-regions.clj")
