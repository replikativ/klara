;; Reuse after recording or load independently in the same REPL.
(let [events (jdk.jfr.consumer.RecordingFile/readAllEvents
              (java.nio.file.Path/of "/tmp/klara-s21-regions.jfr" (make-array String 0)))
      compilations (vec (for [e events
                              :when (= "jdk.Compilation" (.getName (.getEventType e)))
                              :let [m (.getValue e "method")]]
                          {:id (.getInt e "compileId")
                           :class (.getName (.getType m)) :method (.getName m)
                           :compiler (.getString e "compiler")
                           :osr (.getBoolean e "isOsr") :code-size (.getValue e "codeSize")}))
      by-id (into {} (map (juxt :id :compiler) compilations))
      summary {:java-home (System/getProperty "java.home")
               :java-version (System/getProperty "java.version")
               :vm-args (vec (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean)))
               :event-counts (frequencies (map #(.getName (.getEventType %)) events))
               :compilations (filterv #(re-find #"typedprobe|body" (:class %)) compilations)
               :direct-g-inlining
               (frequencies
                (for [e events :when (= "jdk.CompilerInlining" (.getName (.getEventType e)))
                      :let [c (.getValue e "callee")]
                      :when (= "direct_g" (.getString c "name"))]
                  {:compiler (get by-id (.getInt e "compileId") :unrecorded)
                   :success (.getBoolean e "succeeded") :message (.getString e "message")}))}]
  (spit "experiments/typed_jit/s21-jfr-summary.edn" (pr-str summary))
  (println :jfr-summary-saved))
