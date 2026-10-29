(ns kmap.defop
  "Minimal `defop :single`: dispatch on the class of arg0 through an inline
  cache (two monomorphic slots) that falls back to an immutable
  open-addressed class->fn table (megamorphic). Extending an op makes a new
  version: the method map is replaced and the cache is reset. Ambiguous
  interface matches are errors (extensions have owners, D §5)."
  (:import [clojure.lang IFn]))

(set! *warn-on-reflection* true)

;; Immutable cache snapshot, published through one volatile field.
(deftype Cache [^Class c0 ^IFn f0 ^Class c1 ^IFn f1 ^objects tkeys ^objects tvals ^int mask])

(def ^:private empty-cache (Cache. nil nil nil nil nil nil -1))

(defn- table-get [^Cache ic ^Class c]
  (let [mask (.-mask ic)]
    (when-not (neg? mask)
      (let [^objects ks (.-tkeys ic)]
        (loop [i (bit-and (System/identityHashCode c) mask)]
          (let [k (aget ks i)]
            (cond (identical? k c) (aget ^objects (.-tvals ic) i)
                  (nil? k) nil
                  :else (recur (bit-and (unchecked-inc-int i) mask)))))))))

(defn- cache-with
  "New snapshot with c->f added: fill IC slot 0, then 1, then the table."
  ^Cache [^Cache ic ^Class c f]
  (cond
    (nil? (.-c0 ic)) (Cache. c f nil nil nil nil -1)
    (nil? (.-c1 ic)) (Cache. (.-c0 ic) (.-f0 ic) c f nil nil -1)
    :else
    (let [old (when-not (neg? (.-mask ic))
                (keep-indexed (fn [i k] (when k [k (aget ^objects (.-tvals ic) i)]))
                              (.-tkeys ic)))
          entries (cons [c f] old)
          cap (Integer/highestOneBit (int (max 8 (* 4 (count entries)))))
          ks (object-array cap) vs (object-array cap) mask (dec cap)]
      (doseq [[k v] entries]
        (loop [i (bit-and (System/identityHashCode k) mask)]
          (if (nil? (aget ks i))
            (do (aset ks i k) (aset vs i v))
            (recur (bit-and (inc i) mask)))))
      (Cache. (.-c0 ic) (.-f0 ic) (.-c1 ic) (.-f1 ic) ks vs (int mask)))))

(defn- resolve-impl [op-name methods ^Class c]
  (or (some #(get methods %) (take-while #(and (some? %) (not= Object %)) (iterate #(.getSuperclass ^Class %) c)))
      (let [hits (distinct (keep #(get methods %) (disj (supers c) Object)))]
        (when (next hits)
          (throw (ex-info (str op-name ": ambiguous dispatch for " c) {:class c})))
        (first hits))
      (get methods Object)
      (throw (IllegalArgumentException. (str "No implementation of op " op-name " for " c)))))

(definterface IOp
  (^clojure.lang.IFn lookup [x])
  (^clojure.lang.IFn miss [^Class c])
  (extend [^Class c f])
  (methods []))

(deftype SingleOp [op-name ^:volatile-mutable methods ^:volatile-mutable ^Cache ic]
  IOp
  (lookup [this x]
    (let [c (if (nil? x) Void (.getClass ^Object x))
          ic ic]
      (cond (identical? c (.-c0 ic)) (.-f0 ic)
            (identical? c (.-c1 ic)) (.-f1 ic)
            :else (or (table-get ic c) (.miss this c)))))
  (miss [_ c]
    (let [f (resolve-impl op-name methods c)]
      (set! ic (cache-with ic c f))     ; benign race: last snapshot wins
      f))
  (extend [this c f]
    ;; new version: replace the method map, then drop all cached dispatch.
    ;; (Concurrent extends may race; a real impl serializes extends.)
    (set! methods (assoc methods c f))
    (set! ic empty-cache)
    this)
  (methods [_] methods)

  IFn
  (invoke [this x] (.invoke (.lookup this x) x))
  (invoke [this x a] (.invoke (.lookup this x) x a))
  (invoke [this x a b] (.invoke (.lookup this x) x a b))
  (applyTo [this args] (.applyTo (.lookup this (first args)) args))

  Object
  (toString [_] (str "#op " op-name)))

(defn make-op [op-name] (SingleOp. op-name {} empty-cache))

(defmacro defop
  "(defop name :single [x & args]) declares an op dispatching on (class x).
  Only :single is implemented here. Re-evaluating keeps existing methods."
  [name fragment params & [doc]]
  (assert (= fragment :single) "only :single in this prototype")
  `(defonce ~(vary-meta name assoc :arglists `'(~params) :doc doc)
     (make-op '~name)))

(defn extend-op!
  "Add or replace op's implementation for class c (a new op version)."
  [^SingleOp op ^Class c f] (.extend op c f))

(defmacro defimpl
  "(defimpl op Class [x & args] body...)"
  [op cls params & body]
  `(extend-op! ~op ~(if (nil? cls) `Void cls) (fn ~params ~@body)))
