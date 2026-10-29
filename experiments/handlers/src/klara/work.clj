(ns klara.work
  "Ops shared by all benchmarks and the unit of 'work' a handler clause does."
  (:require [klara.fx :as fx]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(fx/defop tick)
(fx/defop unused)
(fx/defop stop)
(fx/defop choose)
(fx/defop observe)
(fx/defop u0) (fx/defop u1) (fx/defop u2) (fx/defop u3) (fx/defop u4)
(fx/defop u5) (fx/defop u6) (fx/defop u7) (fx/defop u8) (fx/defop u9)

;; The work: one xorshift-multiply step on a mutable field (nonlinear, so the
;; JIT cannot find a closed form for a loop of them). It forms a loop-carried
;; dependency chain (~1 ns), so the JIT cannot fold the loop away, but the
;; field store can be kept in a register when everything is inlined.
(definterface IBox
  (add [x])
  (^long get []))

(defprotocol PAdd
  (padd [b x]))

(deftype Box [^:unsynchronized-mutable ^long n]
  IBox
  (add [_ x] (set! n (+ (* (bit-xor n (unsigned-bit-shift-right n 31)) 6364136223846793005) (long x))) n)
  (get [_] n)
  PAdd
  (padd [_ x] (set! n (+ (* (bit-xor n (unsigned-bit-shift-right n 31)) 6364136223846793005) (long x))) n))

(defn box ^IBox [] (Box. 0))

(defn add-fn
  "The direct-call baseline."
  [^IBox b x]
  (.add b x))
