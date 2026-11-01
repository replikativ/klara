(ns klara.runtime.prims
  "Host primitives whose Clojure implementation disagrees with Klara's
  specification (spec/L0-core.md#evaluation, L0.eval.host).

  Clojure 1.12's boxed subtraction negates its second argument first, so
  (apply - [-4 Long/MIN_VALUE]) throws although the result fits; the inlined
  primitive path returns it. Klara specifies checked 64-bit arithmetic: an
  overflow exactly when the result is out of range. Found by the
  differential test against the formal semantics (spec/formal)."
  (:refer-clojure :exclude [-]))

(defn same?
  "Value speculation guard (L4.check.speculate-value): equal and of the same
   class, so that the speculated value cannot be told apart from the real one.
   Only simple immutable values qualify."
  [x c]
  (or (identical? x c)
      (and (= (class x) (class c))
           (cond
             (or (nil? c) (keyword? c) (string? c) (boolean? c) (symbol? c) (char? c)
                 (instance? Long c) (instance? Double c)) (= x c)
             (or (vector? c) (seq? c)) (and (= (count x) (count c)) (every? true? (map same? x c)))
             (map? c) (and (= (count x) (count c))
                           (every? (fn [[k v]] (and (contains? x k) (same? (get x k) v))) c))
             (set? c) (= x c)
             :else false))))

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
