(ns worlds.score)

;; An ordinary Clojure namespace. Nothing here is Klara-specific.
(def adjustment 1)

(defn score [x]
  (+ x adjustment))
