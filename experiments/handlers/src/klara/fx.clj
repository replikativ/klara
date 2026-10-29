(ns klara.fx
  "Direct-style effect handlers without continuation capture.

  * Tail-resumptive fast path (A-O8): a handler clause that resumes exactly
    once, in tail position, is just a function. `perform` looks up the
    innermost clause for the op and calls it. Several lookup structures are
    provided so their cost can be compared:

      perform      ThreadLocal<Object[]> evidence vector indexed by op id
                   (Koka-style evidence vector; op ids fixed at defop time)
      perform-g    a global Object[] (not thread safe; lower bound)
      perform-sv   ScopedValue<Object[]> (JDK 25, final API)
      perform-dyn  a ^:dynamic var holding a {op clause} map (Clojure idiom)
      perform-l    ThreadLocal linked list of frames, searched by op
                   (what a naive handler stack does)

  * Abortive handlers: a clause that never resumes. `perform-abort` throws a
    preallocated stackless exception that the matching `handle-abort` frame
    catches by identity.

  Caveat (documented in README): a deep handler's clause must run *outside*
  its own frame, so a clause that itself performs the same op must reach the
  next outer handler. The fast path here does not implement that re-routing
  (none of the benchmarked clauses perform); Koka does it by storing the
  outer evidence in the handler frame, which costs nothing unless the clause
  performs."
  (:import [clojure.lang IFn]
           [java.util.function Supplier]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(def ^:const MAX-OPS 64)

;; ---------------------------------------------------------------------------
;; operations

(defonce ^:private op-counter (atom -1))

(defmacro defop
  "Define an effect operation. Its integer id is fixed at definition time and
  is inlined into every `perform` site as a constant."
  [name]
  (let [id (or (some-> (resolve name) meta :op-id) (swap! op-counter inc))]
    `(def ~(vary-meta name assoc :op-id id) ~id)))

(defn op-id [env sym]
  (let [v (resolve env sym)]
    (or (:op-id (meta v))
        (throw (ex-info (str sym " is not an op") {:sym sym})))))

(defn unhandled [op]
  (throw (ex-info "unhandled effect" {:op op})))

;; ---------------------------------------------------------------------------
;; 1. ThreadLocal evidence vector

(def ^ThreadLocal EV
  (ThreadLocal/withInitial (reify Supplier (get [_] (object-array MAX-OPS)))))

(defmacro perform [op & args]
  (let [id (op-id &env op)]
    `(let [c# (aget ^"[Ljava.lang.Object;" (.get EV) ~id)]
       (if (nil? c#) (unhandled ~id) (.invoke ^IFn c# ~@args)))))

(defmacro handle
  "(handle [op clause ...] body...) installs tail-resumptive clauses."
  [bindings & body]
  (if (empty? bindings)
    `(do ~@body)
    (let [[op clause & more] bindings
          id (op-id &env op)]
      `(let [ev# ^"[Ljava.lang.Object;" (.get EV)
             old# (aget ev# ~id)]
         (aset ev# ~id ~clause)
         (try (handle [~@more] ~@body)
              (finally (aset ev# ~id old#)))))))

;; ---------------------------------------------------------------------------
;; 2. global array (single-threaded lower bound)

(def ^"[Ljava.lang.Object;" G (object-array MAX-OPS))

(defmacro perform-g [op & args]
  (let [id (op-id &env op)]
    `(let [c# (aget G ~id)]
       (if (nil? c#) (unhandled ~id) (.invoke ^IFn c# ~@args)))))

(defmacro handle-g [[op clause] & body]
  (let [id (op-id &env op)]
    `(let [old# (aget G ~id)]
       (aset G ~id ~clause)
       (try ~@body (finally (aset G ~id old#))))))

;; ---------------------------------------------------------------------------
;; 3. ScopedValue (immutable evidence vector, copied on handle)

(def ^java.lang.ScopedValue SV (java.lang.ScopedValue/newInstance))
(def ^"[Ljava.lang.Object;" EMPTY (object-array MAX-OPS))

(defmacro perform-sv [op & args]
  (let [id (op-id &env op)]
    `(let [c# (aget ^"[Ljava.lang.Object;" (.orElse SV EMPTY) ~id)]
       (if (nil? c#) (unhandled ~id) (.invoke ^IFn c# ~@args)))))

(defmacro handle-sv [[op clause] & body]
  (let [id (op-id &env op)]
    `(let [ev# ^"[Ljava.lang.Object;" (aclone ^"[Ljava.lang.Object;" (.orElse SV EMPTY))]
       (aset ev# ~id ~clause)
       (.call (java.lang.ScopedValue/where SV ev#)
              (reify java.lang.ScopedValue$CallableOp
                (call [_#] ~@body))))))

;; ---------------------------------------------------------------------------
;; 4. dynamic var with a map

(def ^:dynamic *handlers* {})

(defmacro perform-dyn [op & args]
  `(let [c# (get *handlers* ~op)]
     (if (nil? c#) (unhandled ~op) (.invoke ^IFn c# ~@args))))

(defmacro handle-dyn [[op clause] & body]
  `(binding [*handlers* (assoc *handlers* ~op ~clause)] ~@body))

;; ---------------------------------------------------------------------------
;; 5. linked-list handler stack, searched at perform time

(deftype Frame [^long op clause next])

(def ^ThreadLocal LST (ThreadLocal.))

(defn find-clause [^long op]
  (loop [^Frame f (.get LST)]
    (cond (nil? f) (unhandled op)
          (== op (.-op f)) (.-clause f)
          :else (recur (.-next f)))))

(defmacro perform-l [op & args]
  (let [id (op-id &env op)]
    `(.invoke ^IFn (find-clause ~id) ~@args)))

(defmacro handle-l [[op clause] & body]
  (let [id (op-id &env op)]
    `(let [old# (.get LST)]
       (.set LST (Frame. ~id ~clause old#))
       (try ~@body (finally (.set LST old#))))))

;; ---------------------------------------------------------------------------
;; Abortive handlers: preallocated stackless exception

(definterface IAbort
  (frame [])
  (value [])
  (set [frame value]))

;; One stackless exception object per thread, reused; the catching frame
;; recognises its own abort by the frame token.
(def ^ThreadLocal ABORT
  (ThreadLocal/withInitial
   (reify Supplier
     (get [_]
       (let [st (object-array 2)]
         (proxy [RuntimeException klara.fx.IAbort] [nil nil false false]
           (frame [] (aget st 0))
           (value [] (aget st 1))
           (set [f v] (aset st 0 f) (aset st 1 v) this)))))))

;; the innermost abort frame token per op, in the evidence vector
(defmacro handle-abort
  "(handle-abort op on-abort-fn body...) ; on-abort-fn receives the value"
  [op on-abort & body]
  (let [id (op-id &env op)]
    `(let [ev# ^"[Ljava.lang.Object;" (.get EV)
           old# (aget ev# ~id)
           tok# (Object.)]
       (aset ev# ~id tok#)
       (try ~@body
            (catch RuntimeException ex#
              (if (and (instance? IAbort ex#) (identical? tok# (.frame ^IAbort ex#)))
                (~on-abort (.value ^IAbort ex#))
                (throw ex#)))
            (finally (aset ev# ~id old#))))))

(defmacro perform-abort [op v]
  (let [id (op-id &env op)]
    `(let [tok# (aget ^"[Ljava.lang.Object;" (.get EV) ~id)]
       (if (nil? tok#) (unhandled ~id)
           (throw ^Throwable (.set ^IAbort (.get ABORT) tok# ~v))))))

;; reference: what a normal Clojure throw costs
(defmacro handle-abort-exinfo [on-abort & body]
  `(try ~@body
        (catch clojure.lang.ExceptionInfo ex#
          (~on-abort (:value (ex-data ex#))))))

(defn throw-exinfo [v]
  (throw (ex-info "abort" {:value v})))
