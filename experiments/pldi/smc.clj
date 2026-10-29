(ns klara.pldi.smc
  (:require [klara.defs :as d] [klara.world :as w]
            [klara.compile.core :as cc] [klara.stage :as s]
            [klara.authority :as a]))

(def emission
  '(fn [p n] (loop [i n q 0.5]
               (if (> i 0) (recur (dec i) (/ (+ q p) 2.0)) q))))
(def owned-emission
  '(fn [p n] (let [o (own 0.5)]
               (loop [i n]
                 (if (> i 0)
                   (do (update! o (fn [q] (/ (+ q p) 2.0))) (recur (dec i))) nil))
               (freeze o))))
(def forms
  '[(def M 2147483647)
    (defn next-key [key] (mod (* 48271 key) M))
    (defn split-key [key i] (next-key (mod (+ (* 1000003 key) i 1) M)))
    (defn uniform [key] (/ (double key) M))
    (defn model [m ys]
      (loop [x (perform m :choose 0.5) ys ys]
        (perform m :observe (emission (if x 0.9 0.2) 16) (first ys))
        (if (empty? (rest ys)) x
          (recur (perform m :choose (if x 0.8 0.2)) (rest ys)))))
    (defn particle [ys]
      (handle [m {:choose (fn [p k] (fn [key]
                                    (let [key2 (next-key key)]
                                      ((k (< (uniform key2) p)) key2))))
                  :observe (fn [p y k] (fn [key] {:k k :key key :w (if y p (- 1.0 p))}))
                  :return (fn [x] (fn [key] {:done x :key key}))}]
        (model m ys)))
    (defn resume [p key] (((:k p) nil) key))
    (defn resample [ps u]
      (let [n (count ps) total (reduce + (map :w ps))]
        (if (<= total 0) (throw (ex-info "zero particle mass" {})) nil)
        (loop [j 0 i 0 acc (:w (first ps)) out []]
          (if (= j n) out
            (let [pos (* (/ (+ u j) n) total)]
              (if (< acc pos)
                (recur j (inc i) (+ acc (:w (nth ps (inc i)))) out)
                (recur (inc j) i acc (conj out (nth ps i)))))))))
    (defn smc [ys n key]
      (loop [ps (mapv (fn [i] ((particle ys) (split-key key i))) (range n)) key key z 1.0]
        (if (every? (fn [p] (contains? p :done)) ps)
          [(count (filter (fn [p] (true? (:done p))) ps)) z]
          (do
            (if (some (fn [p] (contains? p :done)) ps)
              (throw (ex-info "mixed observation boundaries" {})) nil)
            (let [key2 (next-key key) total (reduce + (map :w ps))
                  kids (resample ps (uniform key2))]
              (recur (vec (map-indexed (fn [i p] (resume p (split-key (:key p) i))) kids))
                     key2 (* z (/ total n))))))))])

(def ys [true true false true false true false false true true true false])
(defn setup [mode]
  (let [wo (w/make-world) cache (s/make-cache)]
    (d/define! wo (list 'def 'emission (if (#{:dynamic :erased} mode) owned-emission emission)))
    (doseq [f forms] (d/define! wo f))
    (let [exe (when (#{:compiled :erased} mode) (cc/compile-def wo 'emission))
          f (d/lookup (w/snapshot wo) 'smc)]
      (when exe (s/install! cache exe))
      {:cache cache :exe exe
       :run #(binding [a/*store* (a/new-store)] (f ys 32 42))})))

;; Independent state-machine Clojure implementation. Particle continuation
;; state is just its Boolean state/key. Same systematic resampling and draws.
(defn next-key [key] (mod (* 48271 key) 2147483647))
(defn split-key [key i] (next-key (mod (+ (* 1000003 key) i 1) 2147483647)))
(defn uniform [key] (/ (double key) 2147483647))
(def host-emission (eval emission))
(defn plain []
  (loop [ps (mapv (fn [i] (let [key (next-key (split-key 42 i))]
                            {:x (< (uniform key) 0.5) :key key})) (range 32))
         obs ys key 42 z 1.0]
    (if (empty? obs) [(count (filter :x ps)) z]
      (let [weighted (mapv (fn [p] (let [q (host-emission (if (:x p) 0.9 0.2) 16)]
                                    (assoc p :w (if (first obs) q (- 1.0 q))))) ps)
            total (reduce + (map :w weighted)) key2 (next-key key)
            kids (loop [j 0 i 0 acc (:w (first weighted)) out []]
                   (if (= j 32) out
                     (if (< acc (* (/ (+ (uniform key2) j) 32) total))
                       (recur j (inc i) (+ acc (:w (nth weighted (inc i)))) out)
                       (recur (inc j) i acc (conj out (nth weighted i))))))
            children (mapv (fn [i p]
                             (let [split (split-key (:key p) i)
                                   draw (if (next obs) (next-key split) split)]
                               {:key draw :x (if (next obs)
                                              (< (uniform draw) (if (:x p) 0.8 0.2)) (:x p))}))
                           (range 32) kids)]
        (recur children (next obs) key2 (* z (/ total 32)))))))
