(ns klara.time
  "Time as an effect (L3.effect.time): (now) performs :time/now, which the
  session and jobs handle with the host's monotonic clock. A handler can
  supply time instead, so code that measures (the investor) can be replayed."
  (:require [klara.effect :refer [perform]]))

(defn now
  "Nanoseconds of a monotonic clock."
  []
  (perform :time/now))
