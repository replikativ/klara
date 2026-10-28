(ns klara.stage-bench
  "S7 measurement (not a test): cost of cache entry on a call-heavy T0
  loop, as a function of the number of world guards an executable has.
  Run: clojure -M:test -m klara.stage-bench [out-file]."
  (:require [klara.stage :as s]
            [klara.defs :as d]
            [klara.world :as w]
            [klara.eval :as ev]))

(defn- median-ms [n thunk]
  (dotimes [_ (max 3 (quot n 2))] (thunk))
  (let [ts (sort (for [_ (range n)]
                   (let [t0 (System/nanoTime)] (thunk) (/ (- (System/nanoTime) t0) 1e6))))]
    (nth ts (quot n 2))))

(defn- world [k]
  (let [wo (w/make-world)
        gs (map #(symbol (str "g" %)) (range k))]
    (doseq [g gs] (d/define! wo (list 'def g '(fn [x] x))))
    ;; f mentions k globals on a branch never taken: k world guards, cheap body
    (d/define! wo (list 'def 'f (list 'fn '[x] (list 'if '(< x 0) (cons '+ (map #(list % 'x) gs)) 'x))))
    (d/define! wo '(def drive (fn [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (f i))) acc)))))
    wo))

(def n 20000)

(defn run-case [k]
  (let [wo (world k) root (w/snapshot wo)
        f (d/lookup root 'f) drive (d/lookup root 'drive)
        term (ev/closure-term f)
        rt #{[:captures []] [:arg 0 :long]}
        bare (s/make-cache)
        _ (s/install! bare (s/executable f rt (fn [x] x) {:bench :s7}))
        guarded (s/make-cache)
        _ (s/install! guarded (s/executable f (into rt (s/world-guards term root)) (fn [x] x) {:bench :s7}))
        expect (reduce + (range n))
        go (fn [cache] (if cache (s/with-cache cache (drive n)) (drive n)))]
    (assert (= expect (go nil) (go bare) (go guarded)))
    (let [t (fn [c] (/ (* 1e6 (median-ms 15 #(go c))) n))
          m 100000
          enter-ns (fn [c] (/ (* 1e6 (median-ms 15 #(dotimes [_ m] (s/enter c f [] [1] root ())))) m))]
      {:world-guards k
       :loop-no-cache-ns (t nil)
       :loop-exe-runtime-guards-only-ns (t bare)
       :loop-exe-with-world-guards-ns (t guarded)
       :enter-runtime-guards-only-ns (enter-ns bare)
       :enter-with-world-guards-ns (enter-ns guarded)})))

(defn bench! []
  (vec (for [k [0 8 32 128]] (run-case k))))

(defn -main [& [out]]
  (let [rs (bench!)
        s (with-out-str
            (println "loop-*: ns per T0 loop iteration (one entry of f through the cache), n =" n)
            (println "enter-*: ns per direct klara.stage/enter call (hit), same root every call")
            (doseq [r rs] (prn r)))]
    (print s)
    (when out (spit out s))
    (shutdown-agents)))
