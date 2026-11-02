;; rules: L3.job.resumed L3.job.resume
;; expect: [:done [[:io/print "once\n"]] :L3.job.resumed]
(ns e-resumed (:require [klara.job :as job]))
(def o (job/run {:budget {:steps 30}}
                (fn [] (loop [i 0] (if (< i 100) (recur (inc i)) nil)) (println "once") :ok)))
(def r (job/resume o {:steps 1000}))
[(:status r) (:intents r)
 (try (job/resume o {:steps 1000}) nil (catch clojure.lang.ExceptionInfo e (:rule (ex-data e))))]
