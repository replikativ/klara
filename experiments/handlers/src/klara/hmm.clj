(ns klara.hmm
  "A 20-step two-state HMM with binary observations, written once (as a
  macro template) and instantiated in each handler style. Every step does
  one `choose` (latent state) and one `observe` (emission log-likelihood):
  40 performs per execution, 20 latent binary choices, 2^20 paths.

  Handlers:
    importance sampling (one-shot, tail-resumptive): direct / fast / cps / loom
    exact enumeration (multi-shot):  direct DFS / cps (resume k twice) /
                                     replay (re-execute with a choice prefix)
    SMC with multinomial-free systematic resampling (multi-shot: a resampled
    particle's continuation is resumed once per offspring):
                                     cps / replay (re-execute prefix, abort
                                     at the t-th observe)"
  (:require [klara.fx :as fx]
            [klara.cps :as c]
            [klara.loom :as l]
            [klara.work :refer [choose observe stop]]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(def ^:const T 20)
(def ^"[J" YS (long-array [1 1 0 1 1 1 0 0 0 1 0 0 0 0 1 1 1 0 1 1]))
;; p(z_t = 1 | z_{t-1}); prev = -1 means t = 0
(defn prior-p1 ^double [^long prev]
  (case prev -1 0.5 0 0.1 0.8))
;; emission log-likelihood table, index z*2+y; p(y=1|z=0)=0.2, p(y=1|z=1)=0.75
(def ^"[D" LL (double-array [(Math/log 0.8) (Math/log 0.2) (Math/log 0.25) (Math/log 0.75)]))
(defn ll ^double [^long z ^long y] (aget LL (+ (* 2 z) y)))

(defmacro hmm-body
  "The model. `perform` is the fully qualified perform macro/fn to use."
  [perform]
  `(loop [t# 0 prev# -1 acc# 0]
     (if (< t# T)
       (let [z# (long (~perform choose (prior-p1 prev#)))
             _# (~perform observe (ll z# (aget YS t#)))]
         (recur (inc t#) z# (+ acc# z#)))
       acc#)))

(defn hmm-fast [] (hmm-body klara.fx/perform))
(defn hmm-loom [] (hmm-body klara.loom/perform))
(def hmm-cps (c/cps (hmm-body klara.cps/perform)))

;; ---------------------------------------------------------------------------
;; rng: xorshift64, state in a long[1]

(defn next-double ^double [^longs s]
  (let [x (aget s 0)
        x (bit-xor x (bit-shift-left x 13))
        x (bit-xor x (unsigned-bit-shift-right x 7))
        x (bit-xor x (bit-shift-left x 17))]
    (aset s 0 x)
    (* (double (unsigned-bit-shift-right x 11)) 1.1102230246251565E-16)))

(defn bern ^long [^longs s ^double p] (if (< (next-double s) p) 1 0))

(defn summarize-is
  "[log-evidence-estimate posterior-mean-of-#ones]"
  [^doubles lws ^longs vals]
  (let [n (alength lws)
        m (areduce lws i m Double/NEGATIVE_INFINITY (Math/max m (aget lws i)))
        z (areduce lws i z 0.0 (+ z (Math/exp (- (aget lws i) m))))
        zv (areduce lws i zv 0.0 (+ zv (* (aget vals i) (Math/exp (- (aget lws i) m)))))]
    [(+ m (Math/log (/ z n))) (/ zv z)]))

;; ---------------------------------------------------------------------------
;; exact reference: forward algorithm

(defn forward []
  (let [a (double-array 2)]
    (dotimes [z 2]
      (aset a z (* 0.5 (Math/exp (ll z (aget YS 0))))))
    (loop [t 1 ^doubles a a]
      (if (< t T)
        (let [b (double-array 2)]
          (dotimes [z 2]
            (aset b z (* (Math/exp (ll z (aget YS t)))
                         (+ (* (aget a 0) (if (== z 1) 0.1 0.9))
                            (* (aget a 1) (if (== z 1) 0.8 0.2))))))
          (recur (inc t) b))
        (Math/log (+ (aget a 0) (aget a 1)))))))

;; ---------------------------------------------------------------------------
;; importance sampling (likelihood weighting), one-shot

(defn is-direct [^long n ^long seed]
  (let [s (long-array [seed]) lws (double-array n) vals (long-array n)]
    (dotimes [i n]
      (loop [t 0 prev -1 acc 0 w 0.0]
        (if (< t T)
          (let [z (bern s (prior-p1 prev))]
            (recur (inc t) z (+ acc z) (+ w (ll z (aget YS t)))))
          (do (aset vals i acc) (aset lws i w)))))
    (summarize-is lws vals)))

(defn is-fast [^long n ^long seed]
  (let [s (long-array [seed]) w (double-array 1) lws (double-array n) vals (long-array n)]
    (fx/handle [choose (fn [p] (bern s (double p)))
                observe (fn [l] (aset w 0 (+ (aget w 0) (double l))) nil)]
      (dotimes [i n]
        (aset w 0 0.0)
        (aset vals i (long (hmm-fast)))
        (aset lws i (aget w 0))))
    (summarize-is lws vals)))

(defn is-cps [^long n ^long seed]
  (let [s (long-array [seed]) w (double-array 1) lws (double-array n) vals (long-array n)]
    (c/handle [choose (fn [p k] (k (bern s (double p))))
               observe (fn [l k] (aset w 0 (+ (aget w 0) (double l))) (k nil))]
      (dotimes [i n]
        (aset w 0 0.0)
        (aset vals i (long (c/run hmm-cps)))
        (aset lws i (aget w 0))))
    (summarize-is lws vals)))

(defn is-loom [^long n ^long seed]
  (let [s (long-array [seed]) w (double-array 1) lws (double-array n) vals (long-array n)]
    (l/handle [choose (fn [p] (bern s (double p)))
               observe (fn [l] (aset w 0 (+ (aget w 0) (double l))) nil)]
      (dotimes [i n]
        (aset w 0 0.0)
        (aset vals i (long (hmm-loom)))
        (aset lws i (aget w 0))))
    (summarize-is lws vals)))

;; ---------------------------------------------------------------------------
;; exact enumeration, multi-shot

(definterface IEnum
  (go [^long t ^long prev ^double w ^long acc]))

(deftype EnumDirect [^doubles out]
  IEnum
  (go [this t prev w acc]
    (if (< t T)
      (let [p (prior-p1 prev)
            y (aget YS t)]
        (.go this (inc t) 0 (+ w (Math/log (- 1.0 p)) (ll 0 y)) acc)
        (.go this (inc t) 1 (+ w (Math/log p) (ll 1 y)) (inc acc)))
      (let [e (Math/exp w)]
        (aset out 0 (+ (aget out 0) e))
        (aset out 1 (+ (aget out 1) (* e acc)))
        nil))))

(defn finish-enum [^doubles out]
  [(Math/log (aget out 0)) (/ (aget out 1) (aget out 0))])

(defn enum-direct []
  (let [out (double-array 2)]
    (.go (EnumDirect. out) 0 -1 0.0 0)
    (finish-enum out)))

(defn enum-cps
  "Multi-shot: the choose clause resumes the same continuation k twice."
  []
  (let [w (double-array 1) out (double-array 2)]
    (c/handle [choose (fn [p k]
                        (let [p (double p) w0 (aget w 0)]
                          (aset w 0 (+ w0 (Math/log (- 1.0 p))))
                          (c/drive (k 0))
                          (aset w 0 (+ w0 (Math/log p)))
                          (c/drive (k 1))
                          nil))
               observe (fn [l k] (aset w 0 (+ (aget w 0) (double l))) (k nil))]
      (c/drive (hmm-cps (fn [v]
                          (let [e (Math/exp (aget w 0))]
                            (aset out 0 (+ (aget out 0) e))
                            (aset out 1 (+ (aget out 1) (* e (long v))))
                            nil))
                        c/rethrow)))
    (finish-enum out)))

(defn enum-replay
  "Re-execution: run the direct-style program once per path, replaying a
  choice prefix and taking 0 at fresh sites; then backtrack to the last 0."
  []
  (let [tr (long-array 64) plen (long-array 1) pos (long-array 1)
        w (double-array 1) out (double-array 2)]
    (fx/handle [choose (fn [p]
                         (let [i (aget pos 0) p (double p)
                               z (if (< i (aget plen 0)) (aget tr i) 0)]
                           (aset tr i z)
                           (aset pos 0 (inc i))
                           (aset w 0 (+ (aget w 0) (Math/log (if (== z 1) p (- 1.0 p)))))
                           z))
                observe (fn [l] (aset w 0 (+ (aget w 0) (double l))) nil)]
      (loop []
        (aset pos 0 0)
        (aset w 0 0.0)
        (let [v (long (hmm-fast)) e (Math/exp (aget w 0))]
          (aset out 0 (+ (aget out 0) e))
          (aset out 1 (+ (aget out 1) (* e v)))
          (let [j (long (loop [j (dec (aget pos 0))]
                          (cond (neg? j) -1
                                (zero? (aget tr j)) j
                                :else (recur (dec j)))))]
            (when-not (neg? j)
              (aset tr j 1)
              (aset plen 0 (inc j))
              (recur))))))
    (finish-enum out)))

;; ---------------------------------------------------------------------------
;; SMC with systematic resampling

(defn log-mean-exp ^double [^doubles ws]
  (let [n (alength ws)
        m (areduce ws i m Double/NEGATIVE_INFINITY (Math/max m (aget ws i)))
        z (areduce ws i z 0.0 (+ z (Math/exp (- (aget ws i) m))))]
    (+ m (Math/log (/ z n)))))

(defn systematic
  "Ancestor indices into anc, from log weights ws."
  [^doubles ws ^longs anc ^longs s]
  (let [n (alength ws)
        m (areduce ws i m Double/NEGATIVE_INFINITY (Math/max m (aget ws i)))
        z (areduce ws i z 0.0 (+ z (Math/exp (- (aget ws i) m))))
        u (next-double s)]
    (loop [i 0 j 0 cum (/ (Math/exp (- (aget ws 0) m)) z)]
      (when (< i n)
        (let [target (/ (+ i u) n)]
          (if (and (< cum target) (< j (dec n)))
            (let [j (inc j)] (recur i j (+ cum (/ (Math/exp (- (aget ws j) m)) z))))
            (do (aset anc i j) (recur (inc i) j cum))))))))

(defn smc-cps
  "Particles suspend at each observe (the clause stores k and does not
  resume); after resampling each surviving continuation is resumed once per
  offspring: multi-shot."
  [^long n ^long seed]
  (let [s (long-array [seed]) ks (object-array n) ks2 (object-array n)
        ws (double-array n) vals (long-array n) anc (long-array n)
        cur (long-array 1) logz (double-array 1)
        done (fn [v] (aset vals (aget cur 0) (long v)) nil)]
    (c/handle [choose (fn [p k] (k (bern s (double p))))
               observe (fn [l k]
                         (let [i (aget cur 0)]
                           (aset ws i (+ (aget ws i) (double l)))
                           (aset ks i k)
                           nil))]
      (dotimes [i n]
        (aset cur 0 i)
        (c/drive (hmm-cps done c/rethrow)))
      (loop [t 0]
        (when (< t T)
          (aset logz 0 (+ (aget logz 0) (log-mean-exp ws)))
          (systematic ws anc s)
          (dotimes [i n] (aset ks2 i (aget ks (aget anc i))))
          (System/arraycopy ks2 0 ks 0 n)
          (java.util.Arrays/fill ws 0.0)
          (dotimes [i n]
            (aset cur 0 i)
            (c/drive ((aget ks2 i) nil)))
          (recur (inc t)))))
    [(aget logz 0) (/ (double (areduce vals i a 0 (+ a (aget vals i)))) n)]))

(defn smc-replay
  "Particles are choice traces. To advance particle i to observe t, the
  direct-style program is re-executed from the start, replaying choices
  0..t-1, sampling choice t, and aborting (stackless exception) at the t-th
  observe. O(n T^2) performs instead of O(n T)."
  [^long n ^long seed]
  (let [s (long-array [seed]) tr (long-array (* n T)) tr2 (long-array (* n T))
        ws (double-array n) vals (long-array n) anc (long-array n)
        cur (long-array 1) pos (long-array 1) obs (long-array 1) target (long-array 1)
        logz (double-array 1)]
    (fx/handle [choose (fn [p]
                         (let [i (aget cur 0) j (aget pos 0) base (* i T)
                               z (if (< j (aget target 0))
                                   (aget tr (+ base j))
                                   (let [z (bern s (double p))] (aset tr (+ base j) z) z))]
                           (aset pos 0 (inc j))
                           z))
                observe (fn [l]
                          (let [o (aget obs 0)]
                            (aset obs 0 (inc o))
                            (when (== o (aget target 0))
                              (aset ws (aget cur 0) (double l))
                              (fx/perform-abort stop nil))
                            nil))]
      (loop [t 0]
        (if (< t T)
          (do
            (aset target 0 t)
            (dotimes [i n]
              (aset cur 0 i) (aset pos 0 0) (aset obs 0 0)
              (fx/handle-abort stop identity (hmm-fast)))
            (aset logz 0 (+ (aget logz 0) (log-mean-exp ws)))
            (systematic ws anc s)
            (dotimes [i n]
              (System/arraycopy tr (* (aget anc i) T) tr2 (* i T) (inc t)))
            (System/arraycopy tr2 0 tr 0 (* n T))
            (recur (inc t)))
          ;; final pass: replay full traces for the return value
          (do
            (aset target 0 T)
            (dotimes [i n]
              (aset cur 0 i) (aset pos 0 0) (aset obs 0 0)
              (aset vals i (long (hmm-fast))))))))
    [(aget logz 0) (/ (double (areduce vals i a 0 (+ a (aget vals i)))) n)]))
