(ns kmap.core
  "KMap: a Klara-style persistent map as a JVM class that implements the
  clojure.lang map interfaces (D §4.3), wrapping any delegate
  IPersistentMap (Clojure's PHM by default, or the clean-room CHAMP).

  Clean-room: written from interface signatures obtained by reflection,
  clojure.org documentation and black-box tests. Equality and both hashes
  are computed here, not delegated, so they test the specification rather
  than the delegate. Hashes follow clojure.org/reference/data_structures
  using the public hash fns (hash, mix-collection-hash)."
  (:require [kmap.champ :as champ])
  (:import [clojure.lang IPersistentMap IPersistentCollection IPersistentVector
            Associative ILookup Counted Seqable MapEquivalence IKVReduce
            IReduceInit IMapIterable IFn IHashEq IMeta IObj IEditableCollection
            ITransientMap ITransientAssociative2 ITransientCollection
            MapEntry Util RT Reduced ArityException]
           [java.util Map Map$Entry Iterator]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)

(declare ->KMap ->TKMap kmap?)

;; ---------------------------------------------------------------------------
;; Helpers

(defn- unsupported [] (UnsupportedOperationException. "KMap is immutable"))

(defn- kv-reduce* [^IPersistentMap m f init]
  (if (instance? IKVReduce m)
    (.kvreduce ^IKVReduce m f init)
    (loop [s (seq m) acc init]
      (if s
        (let [^Map$Entry e (first s)
              acc (f acc (.getKey e) (.getValue e))]
          (if (reduced? acc) @acc (recur (next s) acc)))
        acc))))

(defn- entry-hasheq
  "hasheq of a map entry = hasheq of the 2-vector [k v], i.e. the ordered
  collection hash: h = 31*(31*1 + hash k) + hash v, mixed with count 2."
  ^long [k v]
  (let [h (unchecked-int (unchecked-add-int
                          (unchecked-multiply-int 31
                                                  (unchecked-add-int 31 (int (Util/hasheq k))))
                          (int (Util/hasheq v))))]
    (long (mix-collection-hash h 2))))

(defn- compute-hasheq ^long [^IPersistentMap m]
  (let [sum (kv-reduce* m (fn [^long acc k v]
                            (unchecked-add acc (entry-hasheq k v)))
                        0)]
    (long (mix-collection-hash (unchecked-int sum) (.count m)))))

(defn- compute-hashcode
  "java.util.Map#hashCode: sum over entries of (hashCode k) ^ (hashCode v)."
  ^long [^IPersistentMap m]
  (kv-reduce* m (fn [^long acc k v]
                  (unchecked-int
                   (unchecked-add acc
                                  (bit-xor (long (if (nil? k) 0 (.hashCode ^Object k)))
                                           (long (if (nil? v) 0 (.hashCode ^Object v)))))))
              0))

(def ^:private none (Object.))

(defn- map-equiv?
  "Clojure `=` for maps. Black-box behaviour of Clojure maps: the other side
  must be a java.util.Map; an IPersistentMap that is not MapEquivalence
  (e.g. a record) is never equal; sizes match; every key is present on the
  other side with an equiv value."
  [^IPersistentMap m o]
  (cond
    (identical? m o) true
    (not (instance? Map o)) false
    (and (instance? IPersistentMap o) (not (instance? MapEquivalence o))) false
    :else
    (let [^Map om o]
      (and (== (.count m) (.size om))
           (kv-reduce* m (fn [_ k v]
                           (if (and (.containsKey om k)
                                    (Util/equiv v (.get om k)))
                             true
                             (reduced false)))
                       true)))))

(defn- map-equals?
  "java.util.Map#equals contract."
  [^IPersistentMap m o]
  (cond
    (identical? m o) true
    (not (instance? Map o)) false
    :else
    (let [^Map om o]
      (and (== (.count m) (.size om))
           (kv-reduce* m (fn [_ k v]
                           (if (and (.containsKey om k)
                                    (Util/equals v (.get om k)))
                             true
                             (reduced false)))
                       true)))))

(defn- conj-arg
  "Fold the argument of map conj into assoc-fn calls. Black-box behaviour:
  Map.Entry -> one entry; 2-vector -> one entry (other vectors throw);
  nil -> no-op; otherwise a seqable of Map.Entry (e.g. a map)."
  [assoc-fn acc o]
  (cond
    (instance? Map$Entry o)
    (assoc-fn acc (.getKey ^Map$Entry o) (.getValue ^Map$Entry o))

    (instance? IPersistentVector o)
    (let [^IPersistentVector v o]
      (when-not (== 2 (.count v))
        (throw (IllegalArgumentException. "Vector arg to map conj must be a pair")))
      (assoc-fn acc (.nth v 0) (.nth v 1)))

    :else
    (loop [s (seq o) acc acc]
      (if s
        (let [^Map$Entry e (first s)]
          (recur (next s) (assoc-fn acc (.getKey e) (.getValue e))))
        acc))))

(defn- coll-view
  "Read-only java.util.Collection/Set view over a seq-producing thunk."
  [set? size-fn seq-fn contains-fn]
  (if set?
    (proxy [java.util.AbstractSet] []
      (size [] (size-fn))
      (iterator [] (let [^Iterable s (or (seq-fn) ())] (.iterator s)))
      (contains [o] (boolean (contains-fn o))))
    (proxy [java.util.AbstractCollection] []
      (size [] (size-fn))
      (iterator [] (let [^Iterable s (or (seq-fn) ())] (.iterator s))))))

(defn- map-iter ^Iterator [^Iterator it key?]
  (reify Iterator
    (hasNext [_] (.hasNext it))
    (next [_] (let [^Map$Entry e (.next it)] (if key? (.getKey e) (.getValue e))))
    (remove [_] (throw (unsupported)))))

;; ---------------------------------------------------------------------------
;; KMap

(deftype KMap [^IPersistentMap m _meta
               ^:unsynchronized-mutable ^int _hasheq
               ^:unsynchronized-mutable ^int _hash]

  IMeta
  (meta [_] _meta)

  IObj
  (withMeta [this mta] (if (identical? mta _meta) this (KMap. m mta _hasheq _hash)))

  Counted
  (count [_] (.count m))

  Seqable
  (seq [_] (.seq m))

  Iterable
  (iterator [_] (.iterator ^Iterable m))

  ILookup
  (valAt [_ k] (.valAt m k))
  (valAt [_ k nf] (.valAt m k nf))

  IPersistentCollection
  (cons [this o]
    (conj-arg (fn [^IPersistentMap acc k v] (.assoc acc k v)) this o))
  (empty [_] (KMap. (.empty m) _meta 0 0))
  (equiv [this o] (map-equiv? this o))

  Associative
  (containsKey [_ k] (.containsKey m k))
  (entryAt [_ k] (.entryAt m k))

  IPersistentMap
  (assoc [this k v]
    (let [m2 (.assoc m k v)]
      (if (identical? m2 m) this (KMap. m2 _meta 0 0))))
  (assocEx [this k v]
    (if (.containsKey m k)
      (throw (RuntimeException. "Key already present"))
      (.assoc this k v)))
  (without [this k]
    (let [m2 (.without m k)]
      (if (identical? m2 m) this (KMap. m2 _meta 0 0))))

  MapEquivalence

  IKVReduce
  (kvreduce [_ f init] (kv-reduce* m f init))

  IReduceInit
  (reduce [_ f init]
    (kv-reduce* m (fn [acc k v] (f acc (MapEntry/create k v))) init))

  IMapIterable
  (keyIterator [_]
    (if (instance? IMapIterable m)
      (.keyIterator ^IMapIterable m)
      (map-iter (.iterator ^Iterable m) true)))
  (valIterator [_]
    (if (instance? IMapIterable m)
      (.valIterator ^IMapIterable m)
      (map-iter (.iterator ^Iterable m) false)))

  IHashEq
  (hasheq [_]
    (when (zero? _hasheq)
      (set! _hasheq (unchecked-int (compute-hasheq m))))
    _hasheq)

  IEditableCollection
  (asTransient [_]
    (->TKMap (if (instance? IEditableCollection m)
               (.asTransient ^IEditableCollection m)
               ;; fall back: persistent delegate behind a transient facade
               (volatile! m))
             true))

  IFn
  (invoke [_ k] (.valAt m k))
  (invoke [_ k nf] (.valAt m k nf))
  (applyTo [this args]
    (case (RT/boundedLength args 2)
      1 (.valAt m (first args))
      2 (.valAt m (first args) (second args))
      (throw (ArityException. (RT/boundedLength args 20) "KMap"))))
  (call [_] (throw (ArityException. 0 "KMap")))
  (run [_] (throw (ArityException. 0 "KMap")))

  Map
  (size [_] (.count m))
  (isEmpty [_] (zero? (.count m)))
  (containsValue [this v]
    (kv-reduce* m (fn [_ _ x] (if (Util/equals v x) (reduced true) false)) false))
  (get [_ k] (.valAt m k))
  (put [_ _ _] (throw (unsupported)))
  (remove [_ _] (throw (unsupported)))
  (putAll [_ _] (throw (unsupported)))
  (clear [_] (throw (unsupported)))
  (keySet [this]
    (coll-view true #(.count m) #(keys this) #(.containsKey m %)))
  (values [this]
    (coll-view false #(.count m) #(vals this) nil))
  (entrySet [this]
    (coll-view true #(.count m) #(.seq m)
               (fn [o] (and (instance? Map$Entry o)
                            (.containsKey m (.getKey ^Map$Entry o))
                            (Util/equals (.getValue ^Map$Entry o)
                                         (.valAt m (.getKey ^Map$Entry o)))))))

  Object
  (equals [this o] (map-equals? this o))
  (hashCode [_]
    (when (zero? _hash)
      (set! _hash (unchecked-int (compute-hashcode m))))
    _hash)
  (toString [this] (RT/printString this)))

;; Transient wrapper. `t` is an ITransientMap, or a volatile holding a
;; persistent map when the delegate is not editable.
(deftype TKMap [t ^:unsynchronized-mutable edit]
  ITransientMap
  (assoc [this k v]
    (when-not edit (throw (IllegalAccessError. "Transient used after persistent! call")))
    (if (instance? ITransientMap t)
      (let [t2 (.assoc ^ITransientMap t k v)]
        (if (identical? t2 t) this (TKMap. t2 true)))
      (do (vswap! t assoc k v) this)))
  (without [this k]
    (when-not edit (throw (IllegalAccessError. "Transient used after persistent! call")))
    (if (instance? ITransientMap t)
      (let [t2 (.without ^ITransientMap t k)]
        (if (identical? t2 t) this (TKMap. t2 true)))
      (do (vswap! t dissoc k) this)))
  (persistent [_]
    (when-not edit (throw (IllegalAccessError. "Transient used after persistent! call")))
    (set! edit false)
    ;; Black-box: Clojure's persistent! does not carry metadata.
    (KMap. (if (instance? ITransientMap t) (.persistent ^ITransientMap t) @t) nil 0 0))
  (conj [this o]
    (conj-arg (fn [^ITransientMap acc k v] (.assoc acc k v)) this o))
  (count [_] (if (instance? ITransientMap t) (.count ^ITransientMap t) (count @t)))

  ITransientAssociative2
  (containsKey [_ k]
    (if (instance? ITransientMap t)
      (not (identical? none (.valAt ^ILookup t k none)))
      (contains? @t k)))
  (entryAt [this k]
    (let [v (.valAt this k none)]
      (when-not (identical? v none) (MapEntry/create k v))))

  ILookup
  (valAt [_ k] (if (instance? ITransientMap t) (.valAt ^ILookup t k) (get @t k)))
  (valAt [_ k nf] (if (instance? ITransientMap t) (.valAt ^ILookup t k nf) (get @t k nf)))

  IFn
  (invoke [this k] (.valAt this k))
  (invoke [this k nf] (.valAt this k nf)))

;; ---------------------------------------------------------------------------
;; Construction / printing

(defn kmap?
  [x] (instance? KMap x))


(def ^:dynamic *backend*
  "Delegate used by `kmap`: :phm (Clojure PersistentHashMap) or :champ
  (clean-room kmap.champ)."
  :phm)

(defn kmap
  "Wrap a Clojure map. With *backend* :phm the delegate is a
  PersistentHashMap (benchmark baseline); with :champ a kmap.champ/Champ."
  ([] (kmap {}))
  ([m] (cond
         (kmap? m) m
         (identical? *backend* :champ)
         (KMap. (reduce-kv (fn [^IPersistentMap acc k v] (.assoc acc k v)) champ/EMPTY m)
                (meta m) 0 0)
         :else
         (KMap. (if (instance? clojure.lang.PersistentHashMap m) m
                    (into clojure.lang.PersistentHashMap/EMPTY m))
                (meta m) 0 0))))

(defn wrap
  "Wrap an arbitrary IPersistentMap delegate, keeping it as-is."
  [^IPersistentMap m] (KMap. m (meta m) 0 0))

(defn delegate ^IPersistentMap [^KMap km] (.-m km))

(defn deep-kmap
  "Convert every Clojure map in a tree (through maps, vectors, sets, seqs)
  into a KMap. Records are left alone."
  [x]
  (cond
    (record? x) x
    (map? x) (kmap (into (hash-map) (map (fn [[k v]] [(deep-kmap k) (deep-kmap v)])) x))
    (vector? x) (mapv deep-kmap x)
    (set? x) (into #{} (map deep-kmap) x)
    (seq? x) (doall (map deep-kmap x))
    :else x))

(defn deep-clj
  "Inverse of deep-kmap: every KMap becomes a Clojure hash-map."
  [x]
  (cond
    (record? x) x
    (map? x) (into (hash-map) (map (fn [[k v]] [(deep-clj k) (deep-clj v)])) x)
    (vector? x) (mapv deep-clj x)
    (set? x) (into #{} (map deep-clj) x)
    (seq? x) (doall (map deep-clj x))
    :else x))

(defmethod print-method KMap [m ^java.io.Writer w]
  ((get-method print-method clojure.lang.IPersistentMap) m w))
(defmethod print-dup KMap [m ^java.io.Writer w]
  ((get-method print-dup clojure.lang.IPersistentMap) m w))
