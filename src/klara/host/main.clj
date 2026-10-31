(ns klara.host.main
  "Command line: `clojure -M:klara run FILE` and `clojure -M:klara repl`."
  (:require [clojure.java.io :as io]
            [klara.host.api :as k]
            [klara.lang.expand :as ex])
  (:gen-class))

(def default-roots ["src" "lib" "examples"])

(defn- report [^Throwable e]
  (let [d (ex-data e)]
    (binding [*out* *err*]
      (println (str (when (:rule d) (str (name (:rule d)) ": ")) (.getMessage e)))
      (when (:hint d) (println "hint:" (:hint d))))))

(defn run-file [path]
  (let [s (k/session {:roots (cons (str (.getParent (.getAbsoluteFile (io/file path)))) default-roots)})]
    (try (k/load-file s path) 0
         (catch Throwable e (report e) 1))))

(defn repl []
  (let [s (k/session {:roots default-roots})
        r (clojure.lang.LineNumberingPushbackReader. (io/reader System/in))]
    (println "Klara REPL. Ctrl-D exits.")
    (loop []
      (print (str (:ns @s) "=> ")) (flush)
      (let [form (try (ex/read-all r (:ns @s)) (catch Throwable e (report e) ::skip))]
        (cond
          (ex/eof? form) (println)
          (= ::skip form) (recur)
          :else (do (try (prn (klara.runtime.session/eval-form s form))
                         (catch Throwable e (report e)))
                    (recur)))))))

(defn -main [& [cmd path]]
  (case cmd
    "run" (System/exit (run-file path))
    "repl" (repl)
    (do (println "usage: clojure -M:klara run FILE | repl") (System/exit 2))))
