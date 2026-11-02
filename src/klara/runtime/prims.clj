(ns klara.runtime.prims
  "Host primitives whose Clojure implementation disagrees with Klara's
  specification (spec/L0-core.md#evaluation, L0.eval.host).

  Clojure 1.12's boxed subtraction negates its second argument first, so
  (apply - [-4 Long/MIN_VALUE]) throws although the result fits; the inlined
  primitive path returns it. Klara specifies checked 64-bit arithmetic: an
  overflow exactly when the result is out of range. Found by the
  differential test against the formal semantics (spec/formal)."
  (:refer-clojure :exclude [- conj! assoc! dissoc! disj! pop! persistent! transient]))

(defn same-scalar?
  "Scalars a program cannot tell apart: the same class and equal by the
   host's equals, not by `=`, which identifies 0.0 with -0.0 and 1.0M with
   1.00M (L4.check.const)."
  [a b]
  (or (identical? a b)
      (and (some? a) (some? b) (= (class a) (class b)) (.equals ^Object a b))))

(defn same?
  "Value speculation guard (L4.check.speculate-value): x cannot be told apart
   from c. A collection or other object must be c itself (identity is
   observable, and comparing structure could realize lazy sequences); a
   scalar must be equal, of the same class and with the same metadata. Total:
   it never runs Klara code."
  [x c]
  (or (identical? x c)
      (and (or (nil? c) (number? c) (string? c) (keyword? c) (symbol? c) (boolean? c) (char? c))
           (same-scalar? x c)
           (= (meta x) (meta c)))))

(defn -
  ([x] (clojure.core/- x))
  ([x y] (if (and (instance? Long x) (instance? Long y))
           (Math/subtractExact (long x) (long y))
           (clojure.core/- x y)))
  ([x y & more] (reduce - (- x y) more)))

;; Subtraction for compiled code. Clojure's boxed subtraction of two Longs
;; overflows wrongly near Long/MIN_VALUE; its primitive overloads are right.
;; Compiled code calls (.sub SUB a b), and the host compiler picks the
;; overload from what it knows of a and b statically: primitive arithmetic
;; for primitive locals, this namespace's `-` for objects.
(definterface ISub
  (^long sub [^long x ^long y])
  (^double sub [^double x ^double y])
  (^double sub [^long x ^double y])
  (^double sub [^double x ^long y])
  (^Object sub [^Object x ^long y])
  (^Object sub [^long x ^Object y])
  (^Object sub [^Object x ^double y])
  (^Object sub [^double x ^Object y])
  (^Object sub [^Object x ^Object y]))

(deftype Sub []
  ISub
  (^long sub [_ ^long x ^long y] (Math/subtractExact x y))
  (^double sub [_ ^double x ^double y] (clojure.core/- x y))
  (^double sub [_ ^long x ^double y] (clojure.core/- x y))
  (^double sub [_ ^double x ^long y] (clojure.core/- x y))
  (^Object sub [this ^Object x ^long y] (- x (Long/valueOf y)))
  (^Object sub [this ^long x ^Object y] (- (Long/valueOf x) y))
  (^Object sub [_ ^Object x ^double y] (clojure.core/- x y))
  (^Object sub [_ ^double x ^Object y] (clojure.core/- x y))
  (^Object sub [_ ^Object x ^Object y] (- x y)))

(def ^ISub SUB (Sub.))

;; ---------------------------------------------------------------------------
;; Owned updates (L4.check.in-place, L0.surface.transient, design/04-ownership.md)
;;
;; Klara has no transients of its own: `transient` is the identity, and the
;; transient operations act persistently on persistent values, which is what
;; erasure says they mean. Only compiled code the kernel admitted as owned
;; makes real transients, from `own` at a loop's initial value; it freezes
;; every local it hands the interpreter when it leaves (freeze), so the
;; interpreter, and any continuation resumed once or many times, only ever
;; sees persistent values.

(defn transient [x] x)

(defn own
  "Marks the initial value of an owned loop accumulator. The identity, except
   in compiled code admitted as owned, where lowering makes it `owned`."
  [x] x)

(defn owned
  "`own` in compiled code admitted as owned: a transient where one means the
   same as the value once frozen, else the value itself, which the owned
   operations below update persistently. A transient cannot carry metadata
   and only editable collections have one, so nil, lists, sorted collections
   and values with metadata stay persistent (erasure: freeze after own is
   the identity, L4.check.in-place)."
  [x]
  (if (and (instance? clojure.lang.IEditableCollection x) (nil? (meta x)))
    (clojure.core/transient x)
    x))

;; A leave builds one frame per enclosing let, and the same transient is in
;; several; it can be made persistent only once, so freezing remembers.
;; Transients hash by identity; leaves are rare.
(defonce ^:private frozen (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn freeze [x]
  (if (instance? clojure.lang.ITransientCollection x)
    (or (.get ^java.util.Map frozen x)
        (let [v (clojure.core/persistent! x)] (.put ^java.util.Map frozen x v) v))
    x))

(defn persistent! [x] (freeze x))

(defn conj!
  ([c x] (if (instance? clojure.lang.ITransientCollection c) (clojure.core/conj! c x) (conj c x))))

(defn assoc!
  ([c k v] (if (instance? clojure.lang.ITransientAssociative c) (clojure.core/assoc! c k v) (assoc c k v)))
  ([c k v & kvs] (reduce (fn [c [k v]] (assoc! c k v)) (assoc! c k v) (partition 2 kvs))))

(defn dissoc! [c k] (if (instance? clojure.lang.ITransientMap c) (clojure.core/dissoc! c k) (dissoc c k)))

(defn disj! [c k] (if (instance? clojure.lang.ITransientSet c) (clojure.core/disj! c k) (disj c k)))

(defn pop! [c] (if (instance? clojure.lang.ITransientVector c) (clojure.core/pop! c) (pop c)))
