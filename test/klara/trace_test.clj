(ns klara.trace-test
  "L0.trace.positions: errors carry Klara frames with source positions."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(deftest L0-trace-positions
  (testing "interpreted and compiled code report Klara source lines"
    (let [f (doto (io/file (System/getProperty "java.io.tmpdir") (str "klara-trace-" (System/nanoTime) ".clj"))
              (spit "(ns tr (:require [klara.compiler :as compiler]))\n(defn inner [x]\n  (/ x 0))\n(defn outer [x]\n  (+ 1 (inner x)))\n(def interpreted (try (outer 1) (catch Exception e e)))\n(compiler/optimize! 'tr/inner)\n(def compiled (try (outer 2) (catch Exception e e)))\n"))
          s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (k/load-file s (str f))
      (let [frames (fn [e] (->> (.getStackTrace ^Throwable e)
                                (filter #(= (.getFileName ^StackTraceElement %) (.getName f)))
                                (map #(.getLineNumber ^StackTraceElement %))
                                set))
            interpreted (k/eval-string s "tr/interpreted")
            compiled (k/eval-string s "tr/compiled")]
        (is (every? (frames interpreted) [3 5]) (str "interpreted frames " (frames interpreted)))
        (is (contains? (frames compiled) 3) (str "compiled frames " (frames compiled))))
      (.delete f))))
