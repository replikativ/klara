(ns klara.host.api
  "Driving Klara from Clojure: sessions, evaluation and loading
  (design/03-clojure.md#running-klara). Everything a tool or an agent needs
  from the host side."
  (:refer-clojure :exclude [load-file])
  (:require [klara.compile.kernel]
            [klara.runtime.intrinsics]
            [klara.runtime.job]
            [klara.runtime.prepare]
            [klara.runtime.session :as s]
            [klara.runtime.world :as w]))

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

(defn automatic-investor!
  "Let the investor (klara.investor) decide between top-level forms of
   `session`, when profiles report activity, with policy overrides `pol`
   (L4.jit.trigger). Between forms is where a definition would change the
   world anyway; a long-running single form is not interrupted."
  ([session] (automatic-investor! session {}))
  ([session pol]
   (s/require-lib! session (:ns @session) 'klara.investor)
   (swap! session update :after-form (fnil conj [])
          (fn [s _before]
            (when (.getAndSet ^java.util.concurrent.atomic.AtomicBoolean klara.runtime.prepare/activity false)
              (let [nss (vec (remove #(.startsWith (name %) "klara") (keys (w/namespaces (s/current-world s)))))]
                (s/eval-form s (list 'klara.investor/tick! (list 'quote nss) pol))))))
   session))

(defn require-ns
  "Load namespace `ns-sym` from the session's roots."
  [session ns-sym]
  (s/require-lib! session (:ns @session) ns-sym))
