(ns klara.host.main
  "Command line: `clojure -M:klara run FILE` and `clojure -M:klara repl`."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [klara.runtime.session :as session]
            [klara.host.api :as k]
            [klara.lang.expand :as ex])
  (:gen-class))

(def default-roots ["src" "lib" "examples"])

(defn- report [^Throwable e]
  (let [d (ex-data e)]
    (binding [*out* *err*]
      (println (str (when (:rule d) (str (name (:rule d)) ": ")) (.getMessage e)))
      (when (:hint d) (println "hint:" (:hint d))))))

(defn run-file
  "Run the file. With :record, save the profiles of the functions that ran
   to that file; with :aot, compile definitions as they are defined, from
   profiles saved by an earlier run (L4.profile.saved)."
  [path & {:keys [record aot]}]
  (let [s (k/session {:roots (cons (str (.getParent (.getAbsoluteFile (io/file path)))) default-roots)})]
    (when aot (swap! s assoc :aot (edn/read-string (slurp aot))))
    (try (k/load-file s path)
         (when record (spit record (pr-str (session/saved-profiles s))))
         (when aot
           (binding [*out* *err*]
             (println "compiled ahead:" (:aot-outcomes @s))))
         0
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

(defn -main [& [cmd & more]]
  (case cmd
    "run" (let [;; flags take the next word: --record FILE, --aot FILE
                [opts path] (loop [o {} [x & xs :as all] more]
                              (case x
                                "--record" (recur (assoc o :record (first xs)) (rest xs))
                                "--aot" (recur (assoc o :aot (first xs)) (rest xs))
                                [o (first all)]))]
            (System/exit (run-file path :record (:record opts) :aot (:aot opts))))
    "repl" (repl)
    (do (println "usage: clojure -M:klara run [--record PROFILE.edn] [--aot PROFILE.edn] FILE | repl")
        (System/exit 2))))
