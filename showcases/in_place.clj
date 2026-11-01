(ns showcases.in-place
  "Functional but in place.

  `word-counts` is ordinary persistent Clojure: every word makes a new map.
  Among its alternatives the investor finds one that owns the accumulator:
  a transient, updated in place, made persistent at the end. Nobody can
  tell: the kernel admits it only because the accumulator is provably used
  linearly (the ownership judgment) and the persistent program it erases to
  is the reference. The same rewrite of `with-total`, which hands its
  accumulator to another function on every step, is refused."
  (:require [klara.investor :as investor]
            [klara.jit :as jit]
            [klara.own :as own]
            [klara.compiler :as compiler]))

(defn word-counts [words]
  (loop [i 0 counts {}]
    (if (< i (count words))
      (let [w (nth words i)]
        (recur (inc i) (assoc counts w (inc (get counts w 0)))))
      counts)))

(defn total [counts] (reduce + 0 (vals counts)))

(defn with-total [words]
  (loop [i 0 counts {}]
    (if (< i (count words))
      (let [w (nth words i)]
        (recur (inc i) (assoc counts w (+ (get counts w 0) (if (zero? (total counts)) 1 1)))))
      counts)))

(def words (vec (for [i (range 5000)] (str "w" (mod (* i 7919) 2000)))))

(def bean (java.lang.management.ManagementFactory/getThreadMXBean))
(defn allocated [] (.getCurrentThreadAllocatedBytes bean))

(defn measure
  "Milliseconds and bytes allocated per call of f, warmed up."
  [f]
  (dotimes [_ 50] (f))
  (let [b0 (allocated) t0 (System/nanoTime)]
    (dotimes [_ 50] (f))
    [(/ (- (System/nanoTime) t0) 50000000.0) (quot (- (allocated) b0) 50)]))

(dotimes [_ 20] (word-counts words) (with-total (subvec words 0 200)))
(def before (measure #(word-counts words)))
(def expected (word-counts words))

(def decision (investor/consider 'showcases.in-place/word-counts))
(def after (measure #(word-counts words)))
(def refused (jit/prepare 'showcases.in-place/with-total
                          {:specializer own/in-place :certificate {:kind :in-place}}))

(def report
  {:chosen (:chosen decision)
   :evidence (get-in (compiler/explain word-counts) [:evidence])
   :same-result (= expected (word-counts words) (frequencies words))
   :ms-before (first before) :ms-after (first after)
   :bytes-before (second before) :bytes-after (second after)
   :refused (:status refused)
   :why (:message refused)})

(doseq [k [:chosen :evidence :same-result :ms-before :ms-after :bytes-before :bytes-after :refused :why]]
  (println (str (name k) ":") (get report k)))

report
