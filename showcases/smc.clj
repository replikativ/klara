(ns showcases.smc
  "Sequential Monte Carlo with multi-shot handlers and compiled kernels.

  A hidden Markov model with a Boolean state and twelve Boolean
  observations. The model is ordinary Klara code that performs `:choose`
  (a random draw) and `:observe` (an observation, weighting the particle).
  A particle is the model run under a handler: `:choose` draws from the
  particle's key, `:observe` suspends the particle and hands back its
  continuation and weight. Systematic resampling resumes the selected
  parents, several children from the same parent, so a continuation is
  resumed more than once (L3.cont.multishot). Keys are split per child, so
  the run is deterministic and can be checked against an independent
  state-machine implementation in plain Clojure.

  The emission kernel (a numeric recurrence per observation) is compiled;
  the model, the handler and resampling run in the interpreter, and the
  compiled kernel is called from interpreted code under a live handler.
  `run` reports the posterior count of true final states, the normalizer
  (the product of mean weights) and how the kernel ran."
  (:require [klara.effect :refer [perform handle]]
            [klara.compiler :as compiler]))

;; ---------------------------------------------------------------------------
;; Deterministic keys (Park and Miller's minimal standard generator)

(def M 2147483647)
(defn next-key [key] (mod (* 48271 key) M))
(defn split-key [key i] (next-key (mod (+ (* 1000003 key) i 1) M)))
(defn uniform [key] (/ (double key) M))

;; ---------------------------------------------------------------------------
;; The model

;; The emission probability: n steps of a numeric recurrence (the compiled kernel).
(defn emission [p n]
  (loop [i n q 0.5]
    (if (> i 0) (recur (dec i) (/ (+ q p) 2.0)) q)))

(defn model [ys]
  (loop [x (perform :choose 0.5) ys ys]
    (perform :observe (emission (if x 0.9 0.2) 16) (first ys))
    (if (empty? (rest ys))
      x
      (recur (perform :choose (if x 0.8 0.2)) (rest ys)))))

;; A particle: the model under a handler that threads the particle's key.
;; Each clause returns a function of the key; :observe suspends with k.
(defn particle [ys]
  (handle {:choose (fn [k p] (fn [key] (let [key2 (next-key key)] ((k (< (uniform key2) p)) key2))))
           :observe (fn [k p y] (fn [key] {:k k :key key :w (if y p (- 1.0 p))}))
           :return (fn [x] (fn [key] {:done x :key key}))}
    (model ys)))

(defn resume [p key] (((:k p) nil) key))

;; Systematic resampling: n children from the weighted parents.
(defn resample [ps u]
  (let [n (count ps) total (reduce + (map :w ps))]
    (when (<= total 0) (throw (ex-info "zero particle mass" {})))
    (loop [j 0 i 0 acc (:w (first ps)) out []]
      (if (= j n)
        out
        (let [pos (* (/ (+ u j) n) total)]
          (if (< acc pos)
            (recur j (inc i) (+ acc (:w (nth ps (inc i)))) out)
            (recur (inc j) i acc (conj out (nth ps i)))))))))

(defn smc [ys n key]
  (loop [ps (mapv (fn [i] ((particle ys) (split-key key i))) (range n)) key key z 1.0]
    (if (every? (fn [p] (contains? p :done)) ps)
      [(count (filter (fn [p] (true? (:done p))) ps)) z]
      (do
        (when (some (fn [p] (contains? p :done)) ps)
          (throw (ex-info "mixed observation boundaries" {})))
        (let [key2 (next-key key)
              total (reduce + (map :w ps))
              kids (resample ps (uniform key2))]
          (recur (vec (map-indexed (fn [i p] (resume p (split-key (:key p) i))) kids))
                 key2 (* z (/ total n))))))))

(def ys [true true false true false true false false true true true false])

;; ---------------------------------------------------------------------------
;; The showcase

(def interpreted (smc ys 32 42))
(def outcome (compiler/optimize! 'showcases.smc/emission))
(def compiled (smc ys 32 42))

{:interpreted interpreted
 :compiled compiled
 :kernel (:status outcome)
 :kernel-path (do (emission 0.9 16) (:last-path (compiler/explain emission)))}
