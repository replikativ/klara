(ns klara.runtime.prims
  "Host primitives whose Clojure implementation disagrees with Klara's
  specification (spec/L0-core.md#evaluation, L0.eval.host).

  Clojure 1.12's boxed subtraction negates its second argument first, so
  (apply - [-4 Long/MIN_VALUE]) throws although the result fits; the inlined
  primitive path returns it. Klara specifies checked 64-bit arithmetic: an
  overflow exactly when the result is out of range. Found by the
  differential test against the formal semantics (spec/formal)."
  (:refer-clojure :exclude [-]))

(defn -
  ([x] (clojure.core/- x))
  ([x y] (if (and (instance? Long x) (instance? Long y))
           (Math/subtractExact (long x) (long y))
           (clojure.core/- x y)))
  ([x y & more] (reduce - (- x y) more)))
