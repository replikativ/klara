(ns worlds.main
  "Retained worlds: old versions of a program stay usable as values."
  (:require [worlds.score :refer [score]]
            [klara.world :as world]))

(def before (world/current))          ; hold the world in which adjustment = 1

(assert (= 5 (score 4)))

;; Redefine, as one would at a REPL. Late binding: score sees the change.
(in-ns 'worlds.score)
(def adjustment 10)
(in-ns 'worlds.main)

(assert (= 14 (score 4)))

;; The old world is still a value, and means what it meant.
(assert (= 5 (world/in before score 4)))

;; A function taken from the old world remembers it.
(def old-score (world/get before 'worlds.score/score))
(assert (= 5 (old-score 4)))

;; A world can be changed without publishing it: define returns a new world.
(def experiment (world/define (world/current) 'worlds.score/adjustment 100))
(assert (= 104 (world/in experiment score 4)))
(assert (= 14 (score 4)))             ; the session's world is unchanged

(println "worlds: ok")
