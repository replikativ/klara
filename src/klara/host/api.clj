(ns klara.host.api
  "Driving Klara from Clojure: sessions, evaluation and loading
  (design/03-clojure.md#running-klara). Everything a tool or an agent needs
  from the host side."
  (:require [klara.compile.kernel]
            [klara.runtime.intrinsics]
            [klara.runtime.job]
            [klara.runtime.session :as s]))

(defn session
  "A new Klara session. Options: :roots (source directories), :out (writer)."
  ([] (s/new-session))
  ([opts] (s/new-session opts)))

(defn eval-string
  "Evaluate Klara source `src` form by form in `session`; returns the last value."
  [session src]
  (s/eval-string session src))

(defn load-file
  "Evaluate a Klara source file in `session`."
  [session path]
  (s/load-source! session (clojure.java.io/file path)))

(defn require-ns
  "Load namespace `ns-sym` from the session's roots."
  [session ns-sym]
  (s/require-lib! session (:ns @session) ns-sym))
