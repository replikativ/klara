(ns klara.loom
  "One-shot deep handlers on the JDK's internal delimited continuations
  (jdk.internal.vm.Continuation, the mechanism under virtual threads).
  Requires --add-exports java.base/jdk.internal.vm=ALL-UNNAMED.

  The body runs inside a Continuation. `perform` writes (op, arg) into the
  handler's mailbox and yields; the handler loop runs the clause on its own
  stack (outside the body: deep-handler semantics) and resumes with the
  reply. A clause that does not want to resume simply stops running the
  continuation (abort). There is no multi-shot: the JDK continuation
  cannot be copied (Continuation cloning is not part of the JDK)."
  (:require [klara.fx :as fx])
  (:import [clojure.lang IFn]
           [jdk.internal.vm Continuation ContinuationScope]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(def ^ContinuationScope SCOPE (ContinuationScope. "klara"))

;; mailbox of the innermost loom handler on this thread: [op arg reply]
(def ^ThreadLocal MB (ThreadLocal.))

(defn perform* [^long op arg]
  (let [^objects mb (.get MB)]
    (aset mb 0 (Long/valueOf op))
    (aset mb 1 arg)
    (Continuation/yield SCOPE)
    (aget mb 2)))

(defmacro perform [op arg]
  `(perform* ~(fx/op-id &env op) ~arg))

(defn handle*
  "clauses: Object[] indexed by op id of (fn [arg] reply)."
  [^objects clauses body-fn]
  (let [mb (object-array 3)
        res (object-array 1)
        outer (.get MB)
        c (Continuation. SCOPE (reify Runnable
                                 (run [_] (aset res 0 (.invoke ^IFn body-fn)))))]
    (try
      (loop []
        (.set MB mb)
        (.run c)
        (if (.isDone c)
          (aget res 0)
          (let [clause (aget clauses (int (.longValue ^Long (aget mb 0))))]
            ;; clause runs outside the body, with the outer handler installed
            (.set MB outer)
            (aset mb 2 (.invoke ^IFn clause (aget mb 1)))
            (recur))))
      (finally (.set MB outer)))))

(defmacro handle [bindings & body]
  (let [pairs (partition 2 bindings)
        cl (gensym "cl")]
    `(let [~cl (object-array fx/MAX-OPS)]
       ~@(for [[op clause] pairs] `(aset ~cl ~(fx/op-id &env op) ~clause))
       (handle* ~cl (fn [] ~@body)))))
