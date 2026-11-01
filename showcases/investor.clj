(ns showcases.investor
  "The investor decides what to compile.

  A small pricing program: `score` is a polynomial, `rank` scores a
  catalogue and keeps the best item, `banner` formats the result once. After
  a morning of traffic the investor looks at every function: it measures
  what an interpreted call costs on an argument from the profile, prepares
  its alternatives in parallel jobs, measures each, and compiles only where
  the expected gain covers what preparing cost. Measuring by running a
  function is safe: each measurement is a job on a fork of the world.

  The decisions are not obvious, and that is the point: `score` alone gains
  little (entering compiled code costs about what it saves, so the decision
  rests on a margin the investor requires of its measurements), while
  `rank`, which calls it in a loop, gains a lot compiled with `score`
  inlined. The compiled `rank` carries its provenance: the reference, the
  candidate the kernel checked, its premises, the specializer and the
  investor's decision."
  (:require [klara.investor :as investor]
            [klara.compiler :as compiler]))


(defn score [x] (+ (* 3 x x) (* -2 x) 7))

(defn rank [prices]
  (loop [i 0 best nil best-score nil]
    (if (< i (count prices))
      (let [p (nth prices i) s (score p)]
        (if (or (nil? best-score) (> s best-score))
          (recur (inc i) p s)
          (recur (inc i) best best-score)))
      best)))

(defn banner [best] (str "best price today: " best))

(def catalogue (vec (for [i (range 2000)] (- (mod (* i 7919) 2001) 1000))))

(defn ms [f] (let [t (System/nanoTime) r (f)] [(/ (- (System/nanoTime) t) 1000000.0) r]))

;; A morning of traffic.
(dotimes [_ 50] (rank catalogue))
(def before (ms #(rank catalogue)))
(def best (banner (second before)))

;; a short demonstration: explore whatever has passed the baseline (the
;; default policy waits until a definition has spent half a second)
(def decisions (investor/invest! 'showcases.investor {:explore-ns 0}))
(dotimes [_ 20] (rank catalogue))
(def after (ms #(rank catalogue)))

(defn row [d]
  (str (name (:name d)) ": " (name (:decision d))
       (when (:chosen d) (str " with " (name (:chosen d))))
       (when (:interpreted-ns d)
         (str ", interpreted " (:interpreted-ns d) " ns"
              (apply str (for [a (:alternatives d)]
                           (str ", " (name (:name a)) " " (or (:ns-per-call a) (name (:status a))) " ns")))
              ", preparing cost " (quot (:prepare-ns (:spent d)) 1000000) " ms"))))

(doseq [d decisions] (println (row d)))
(println best)
(println "rank:" (first before) "ms before," (first after) "ms after")

{:decisions (into {} (map (juxt :name :decision) decisions))
 :chosen (into {} (keep #(when (:chosen %) [(:name %) (:chosen %)]) decisions))
 :same-result (= (second before) (second after))
 :speedup (/ (first before) (first after))
 :recorded (count (get investor/decisions 'showcases.investor/rank))
 :provenance (:provenance (compiler/explain rank))
 :premises (:premises (compiler/explain rank))}
