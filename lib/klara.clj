(ns klara
  "Introspection for programmers and agents (design/03-clojure.md)."
  (:require [klara.kernel :as kernel]
            [klara.compiler :as compiler]))

(defn retained
  "What the session's roots keep alive (design/01-lifetimes.md#roots)."
  []
  (kernel/retained))

(defn explain
  "How a function is executed: interpreted, compiled, its premises."
  [f]
  (compiler/explain f))
