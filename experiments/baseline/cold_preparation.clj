(ns baseline.cold-preparation
  "Fresh-process lazy loader boundary. Does not preload compiler namespaces."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]))

(defn timed [f]
  (let [start (System/nanoTime) v (f)] {:value v :ns (- (System/nanoTime) start)}))

(defn -main [& [process]]
  (let [runtime (timed #(require 'klara.load 'klara.stage 'klara.world))
        make-world (requiring-resolve 'klara.world/make-world)
        make-cache (requiring-resolve 'klara.stage/make-cache)
        load! (requiring-resolve 'klara.load/load-string!)
        sha256 (requiring-resolve 'klara.core/sha256)
        hashes (into {} (for [p (concat ["deps.edn" "experiments/baseline/cold_preparation.clj"]
                                        (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                             [p (sha256 (slurp p))]))
        source "(def sum (fn [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc i)) acc))))"
        compiler-before? (boolean (find-ns 'klara.compile.prepare))
        plain (timed #(load! (make-world) source {:path "cold.clj"}))
        compiler-after-off? (boolean (find-ns 'klara.compile.prepare))
        cache (make-cache) w (make-world)
        first-prepared (timed #(load! w source {:path "cold.clj" :prepare :baseline :cache cache}))
        second-prepared (timed #(load! w source {:path "cold.clj" :prepare :baseline :cache cache}))
        report {:process (or process "0") :java (System/getProperty "java.runtime.version")
                :runtime-require-ns (:ns runtime) :source-sha256 hashes
                :jvm-arguments (vec (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean)))
                :compiler-before? compiler-before? :compiler-after-off? compiler-after-off?
                :plain-load-ns (:ns plain)
                :first-prepared-load first-prepared :second-prepared-load second-prepared}
        output (str "target/investment/cold-" (or process "0") ".edn")]
    (assert (false? compiler-before?)) (assert (false? compiler-after-off?))
    (doseq [result [first-prepared second-prepared]]
      (assert (= :installed (get-in result [:value :preparation :definitions 0 :status]))))
    (io/make-parents output) (spit output (with-out-str (pp/pprint report)))
    (prn report))
  (shutdown-agents))
