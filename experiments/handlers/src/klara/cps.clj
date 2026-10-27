(ns klara.cps
  "General (one-shot and multi-shot) continuations by selective CPS transform,
  using partial-cps's `invert` with `perform` registered as the only
  breakpoint. Only code that can reach a `perform` is transformed; the rest
  stays direct-style Clojure.

  A clause receives the op's argument and the continuation `k`. It may call
  `k` once (one-shot), not at all (abort / suspend), or several times
  (multi-shot): a partial-cps continuation is an ordinary closure over
  immutable locals, so re-invoking it is sound as long as the captured
  context holds no mutable resources (Klara core v1 §1).

  Handler clauses live in a ThreadLocal evidence vector indexed by op id,
  exactly like klara.fx, but with the extra `k` argument."
  (:require [is.simm.partial-cps.ioc :as ioc]
            [is.simm.partial-cps.runtime :as rt]
            [klara.fx :as fx])
  (:import [clojure.lang IFn]
           [is.simm.partial_cps.runtime Thunk]
           [java.util.function Supplier]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(defn perform
  "Effect operation; only valid inside `cps`."
  [_op & _args]
  (throw (ex-info "perform outside cps" {})))

(def ^ThreadLocal CEV
  (ThreadLocal/withInitial (reify Supplier (get [_] (object-array fx/MAX-OPS)))))

(defn perform-handler [ctx r _e]
  (fn [[op arg]]
    (let [id (fx/op-id (:env ctx) op)]
      `(let [c# (aget ^"[Ljava.lang.Object;" (.get CEV) ~id)]
         (if (nil? c#) (fx/unhandled ~id) (.invoke ^IFn c# ~arg ~r))))))

(def breakpoints {`perform `perform-handler})

(defmacro cps
  "A CPS computation: a fn of [resolve reject]."
  [& body]
  (let [r (gensym "r") e (gensym "e")
        params {:r r :e e :env &env :breakpoints breakpoints}]
    `(fn [~r ~e] ~(ioc/invert params (cons 'do body)))))

(defn drive
  "Run trampoline bounces until a non-thunk value is returned."
  [x]
  (loop [x x]
    (if (instance? Thunk x) (recur ((.-f ^Thunk x))) x)))

(defn rethrow [e] (throw e))

(defn run
  "Run cps computation `c` to completion; returns its result (assuming all
  clauses resume synchronously)."
  [c]
  (let [res (object-array 1)]
    (drive (c (fn [v] (aset res 0 v) nil) rethrow))
    (aget res 0)))

(defmacro handle
  "(handle [op clause ...] body...) installs CPS clauses (fn [arg k]) for the
  dynamic extent of body. Body typically calls `run`/`drive`."
  [bindings & body]
  (if (empty? bindings)
    `(do ~@body)
    (let [[op clause & more] bindings
          id (fx/op-id &env op)]
      `(let [ev# ^"[Ljava.lang.Object;" (.get CEV)
             old# (aget ev# ~id)]
         (aset ev# ~id ~clause)
         (try (handle [~@more] ~@body)
              (finally (aset ev# ~id old#)))))))
