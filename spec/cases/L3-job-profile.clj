;; rules: L3.job.profile L1.world.names
;; expect: [10 10 20 [jpr/f jpr/g]]
(ns jpr (:require [klara.job :as job] [klara.profile :as profile] [klara.world :as world]))
(defn f [x] (inc x))
(def g 1)
(dotimes [i 10] (f i))
(def a (:count (:entries (profile/snapshot f))))
(job/run {:profile false} (fn [] (dotimes [i 10] (f i))))
(def b (:count (:entries (profile/snapshot f))))
(job/run {} (fn [] (dotimes [i 10] (f i))))
(def c (:count (:entries (profile/snapshot f))))
[a b c (filterv #{'jpr/f 'jpr/g} (world/names (world/current) 'jpr))]
