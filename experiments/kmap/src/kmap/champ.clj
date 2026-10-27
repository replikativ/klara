(ns kmap.champ
  "Clean-room CHAMP (Steindorfer & Vinju, OOPSLA 2015) written from the
  paper's design only: per node two 32-bit bitmaps (dataMap, nodeMap), one
  content array holding key/value pairs from the front and sub-nodes from
  the back (reverse order), 5 hash bits per level, collision nodes once the
  32-bit hash is exhausted, and canonical deletion (a sub-node left with a
  single entry and no sub-nodes is inlined into its parent).

  Keys hash with Clojure's hasheq and compare with Clojure's equiv so the
  map has Clojure key semantics (1 and 1N are the same key). Persistent
  only: KMap provides a transient facade over it."
  (:import [clojure.lang Util MapEntry IPersistentMap IKVReduce Reduced RT]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)

(definterface INode
  (assoc [k v ^int hash ^int shift ^"[Ljava.lang.Object;" added])
  (without [k ^int hash ^int shift])
  (lookup [k ^int hash ^int shift nf])
  (kvreduce [f init])
  (^boolean singleton [])
  (nodeSeq []))

(declare ->BNode ->CNode merge-two)

(defn- idx-data ^long [^long datamap ^long bit]
  (* 2 (Long/bitCount (bit-and datamap (dec bit)))))
(defn- idx-node ^long [^objects arr ^long nodemap ^long bit]
  (- (alength arr) 1 (Long/bitCount (bit-and nodemap (dec bit)))))
(defn- mask ^long [^long hash ^long shift] (bit-and (unsigned-bit-shift-right hash shift) 31))

(defn- arr-insert ^objects [^objects a ^long i x y]
  (let [n (alength a) b (object-array (+ n 2))]
    (System/arraycopy a 0 b 0 i)
    (aset b i x) (aset b (inc i) y)
    (System/arraycopy a i b (+ i 2) (- n i))
    b))

(defn- arr-copy-set ^objects [^objects a ^long i x]
  (let [b (aclone a)] (aset b i x) b))

;; data entry at di (2 slots) -> node at the node position for bit
(defn- data->node ^objects [^objects a ^long di ^long ni-new node]
  ;; ni-new: index in the NEW array (length n-1)
  (let [n (alength a) b (object-array (dec n))]
    (System/arraycopy a 0 b 0 di)
    (System/arraycopy a (+ di 2) b di (- ni-new di))
    (aset b ni-new node)
    (System/arraycopy a (+ ni-new 2) b (inc ni-new) (- n ni-new 2))
    b))

;; node at ni (old array) -> data entry at di (new array, length n+1)
(defn- node->data ^objects [^objects a ni0 di0 k v]
  (let [ni (long ni0) di (long di0) n (alength a) b (object-array (inc n))]
    (System/arraycopy a 0 b 0 di)
    (aset b di k) (aset b (inc di) v)
    (System/arraycopy a di b (+ di 2) (- ni di))
    (System/arraycopy a (inc ni) b (+ ni 2) (- n ni 1))
    b))

(defn- reduce-data [^objects a ^long n f init]
  (loop [i 0 acc init]
    (if (< i n)
      (let [acc (f acc (aget a i) (aget a (inc i)))]
        (if (reduced? acc) acc (recur (+ i 2) acc)))
      acc)))

(deftype BNode [^int datamap ^int nodemap ^objects arr]
  INode
  (assoc [this k v hash shift added]
    (let [bit (bit-shift-left 1 (mask hash shift))]
      (cond
        (not (zero? (bit-and datamap bit)))
        (let [di (idx-data datamap bit) k0 (aget arr di)]
          (if (Util/equiv k k0)
            (if (identical? v (aget arr (inc di))) this
                (BNode. datamap nodemap (arr-copy-set arr (inc di) v)))
            (let [v0 (aget arr (inc di))
                  sub (merge-two k0 v0 (Util/hasheq k0) k v hash (+ shift 5))
                  dm (bit-xor datamap bit) nm (bit-or nodemap bit)
                  ni (- (alength arr) 2 (Long/bitCount (bit-and nm (dec bit))))]
              (aset added 0 true)
              (BNode. dm nm (data->node arr di ni sub)))))

        (not (zero? (bit-and nodemap bit)))
        (let [ni (idx-node arr nodemap bit) ^INode sub (aget arr ni)
              sub2 (.assoc sub k v hash (+ shift 5) added)]
          (if (identical? sub sub2) this (BNode. datamap nodemap (arr-copy-set arr ni sub2))))

        :else
        (do (aset added 0 true)
            (BNode. (bit-or datamap bit) nodemap (arr-insert arr (idx-data datamap bit) k v))))))

  (without [this k hash shift]
    (let [bit (bit-shift-left 1 (mask hash shift))]
      (cond
        (not (zero? (bit-and datamap bit)))
        (let [di (idx-data datamap bit)]
          (if (Util/equiv k (aget arr di))
            (let [n (alength arr) b (object-array (- n 2))]
              (System/arraycopy arr 0 b 0 di)
              (System/arraycopy arr (+ di 2) b di (- n di 2))
              (BNode. (bit-xor datamap bit) nodemap b))
            this))

        (not (zero? (bit-and nodemap bit)))
        (let [ni (idx-node arr nodemap bit) ^INode sub (aget arr ni)
              ^INode sub2 (.without sub k hash (+ shift 5))]
          (cond
            (identical? sub sub2) this
            ;; canonical form: inline a sub-node that holds one entry only
            (.singleton sub2)
            (let [[k1 v1] (first (.nodeSeq sub2))]
              (BNode. (bit-or datamap bit) (bit-xor nodemap bit)
                      (node->data arr ni (idx-data datamap bit) k1 v1)))
            :else (BNode. datamap nodemap (arr-copy-set arr ni sub2))))
        :else this)))

  (lookup [_ k hash shift nf]
    (let [bit (bit-shift-left 1 (mask hash shift))]
      (cond
        (not (zero? (bit-and datamap bit)))
        (let [di (idx-data datamap bit)]
          (if (Util/equiv k (aget arr di)) (aget arr (inc di)) nf))
        (not (zero? (bit-and nodemap bit)))
        (.lookup ^INode (aget arr (idx-node arr nodemap bit)) k hash (+ shift 5) nf)
        :else nf)))

  (kvreduce [_ f init]
    (let [nd (* 2 (Integer/bitCount datamap))
          acc (reduce-data arr nd f init)]
      (loop [i (dec (alength arr)) acc acc]
        (if (or (reduced? acc) (< i nd)) acc
            (recur (dec i) (.kvreduce ^INode (aget arr i) f acc))))))

  (singleton [_] (and (zero? nodemap) (== 1 (Integer/bitCount datamap))))

  (nodeSeq [_]
    (let [nd (* 2 (Integer/bitCount datamap))]
      (concat (for [i (range 0 nd 2)] (MapEntry/create (aget arr (long i)) (aget arr (inc (long i)))))
              (lazy-seq (mapcat #(.nodeSeq ^INode %)
                                (for [i (range (dec (alength arr)) (dec nd) -1)] (aget arr (long i)))))))))

;; Hash-collision node: all keys share the full 32-bit hash.
(deftype CNode [^int hash ^objects arr]
  INode
  (assoc [this k v h shift added]
    (let [n (alength arr)
          i (long (loop [i 0] (cond (>= i n) -1 (Util/equiv k (aget arr i)) i :else (recur (+ i 2)))))]
      (if (neg? i)
        (do (aset added 0 true) (CNode. hash (arr-insert arr n k v)))
        (if (identical? v (aget arr (inc i))) this (CNode. hash (arr-copy-set arr (inc i) v))))))
  (without [this k h shift]
    (let [n (alength arr)
          i (long (loop [i 0] (cond (>= i n) -1 (Util/equiv k (aget arr i)) i :else (recur (+ i 2)))))]
      (if (neg? i) this
          (let [b (object-array (- n 2))]
            (System/arraycopy arr 0 b 0 i)
            (System/arraycopy arr (+ i 2) b i (- n i 2))
            (CNode. hash b)))))
  (lookup [_ k h shift nf]
    (let [n (alength arr)]
      (loop [i 0] (cond (>= i n) nf
                        (Util/equiv k (aget arr i)) (aget arr (inc i))
                        :else (recur (+ i 2))))))
  (kvreduce [_ f init] (reduce-data arr (alength arr) f init))
  (singleton [_] (== 2 (alength arr)))
  (nodeSeq [_] (for [i (range 0 (alength arr) 2)] (MapEntry/create (aget arr (long i)) (aget arr (inc (long i)))))))

(defn- merge-two [k0 v0 h0' k1 v1 h1' shift']
  (let [h0 (long h0') h1 (long h1') shift (long shift')]
  (if (>= shift 32)
    (CNode. (unchecked-int h0) (object-array [k0 v0 k1 v1]))
    (let [m0 (mask h0 shift) m1 (mask h1 shift)]
      (if (== m0 m1)
        (BNode. 0 (unchecked-int (bit-shift-left 1 m0))
                (object-array [(merge-two k0 v0 h0 k1 v1 h1 (+ shift 5))]))
        (BNode. (unchecked-int (bit-or (bit-shift-left 1 m0) (bit-shift-left 1 m1))) 0
                (if (< m0 m1) (object-array [k0 v0 k1 v1]) (object-array [k1 v1 k0 v0]))))))))

(def ^:private empty-node (BNode. 0 0 (object-array 0)))
(def ^:private none (Object.))

;; Root: count + node. Implements just what KMap calls on a delegate.
(deftype Champ [^int cnt ^INode root]
  IPersistentMap
  (assoc [this k v]
    (let [added (object-array 1)
          r (.assoc root k v (Util/hasheq k) 0 added)]
      (if (identical? r root) this
          (Champ. (if (aget added 0) (unchecked-inc-int cnt) cnt) r))))
  (assocEx [this k v]
    (if (.containsKey this k) (throw (RuntimeException. "Key already present")) (.assoc this k v)))
  (without [this k]
    (let [r (.without root k (Util/hasheq k) 0)]
      (if (identical? r root) this (Champ. (unchecked-dec-int cnt) r))))
  (containsKey [_ k] (not (identical? none (.lookup root k (Util/hasheq k) 0 none))))
  (entryAt [_ k] (let [v (.lookup root k (Util/hasheq k) 0 none)]
                   (when-not (identical? v none) (MapEntry/create k v))))
  (valAt [_ k] (.lookup root k (Util/hasheq k) 0 nil))
  (valAt [_ k nf] (.lookup root k (Util/hasheq k) 0 nf))
  (count [_] cnt)
  (cons [this o] (if (instance? java.util.Map$Entry o)
                   (.assoc this (key o) (val o))
                   (reduce (fn [^IPersistentMap m e] (.cons m e)) this (if (vector? o) [(MapEntry/create (o 0) (o 1))] (seq o)))))
  (empty [_] (Champ. 0 empty-node))
  (equiv [this o] (throw (UnsupportedOperationException. "wrap in KMap")))
  (seq [_] (when (pos? cnt) (seq (.nodeSeq root))))
  (iterator [this] (let [^java.lang.Iterable s (or (.seq this) ())] (.iterator s)))

  IKVReduce
  (kvreduce [_ f init] (let [r (.kvreduce root f init)] (if (reduced? r) @r r))))

(def EMPTY (Champ. 0 empty-node))

(defn champ
  "Build a Champ from any map / seq of entries."
  [m] (reduce-kv (fn [^IPersistentMap acc k v] (.assoc acc k v)) EMPTY (into {} m)))
