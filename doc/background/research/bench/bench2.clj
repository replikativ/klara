(set! *warn-on-reflection* true)
(import '[java.util SplittableRandom])
(def N 1000) (def M 1024) (def T 30)
;; Flat value vector: root Object[32] of long[32] leaves, with per-node owner tokens.
;; A node may be written in place iff its owner == the current region token (region uniqueness).
(deftype FV [^objects leaves ^objects owners rootOwner])
(defn ancestors-idx ^ints [^SplittableRandom r n]
  (let [a (int-array n)] (dotimes [i n] (aset a i (.nextInt r (int n)))) a))
(defn thaw ^FV [^FV v tok]
  ;; O(1) if root already owned by tok; else copy the 32-slot spine only (path copy of root)
  (if (identical? (.rootOwner v) tok) v
      (FV. (aclone ^objects (.leaves v)) (object-array 32) tok)))
(defn put! [^FV v ^long i ^long x tok]
  (let [li (bit-shift-right i 5) ^objects ls (.leaves v) ^objects os (.owners v)]
    (when-not (identical? (aget os li) tok)
      (aset ls li (aclone ^longs (aget ls li))) (aset os li tok))
    (aset ^longs (aget ls li) (bit-and i 31) x) v))
(defn run-flat-move [K]
  ;; fork-site counting: the resampler knows offspring counts; the first child inherits (moves) the
  ;; parent's token, duplicates get fresh tokens and path-copy lazily. Region token carried in [tok v].
  (let [r (SplittableRandom. 42) z (FV. (into-array Object (repeatedly 32 #(long-array 32))) (object-array 32) nil)]
    (loop [t 0 ps (vec (repeat N [nil z]))]
      (if (= t T) ps
        (let [ps (mapv (fn [[tok v]] (let [tok (or tok (Object.)) v (thaw v tok)]
                                       (dotimes [k K] (put! v (.nextInt r (int M)) k tok))
                                       [tok v])) ps)
              a (ancestors-idx r N) used (boolean-array N)]
          (recur (inc t) (mapv (fn [i] (let [j (aget a (int i)) [tok v] (nth ps j)]
                                         (if (aget used j) [nil v] (do (aset used j true) [tok v]))))
                               (range N))))))))
(defn run-flat [K]
  (let [r (SplittableRandom. 42) z (FV. (into-array Object (repeatedly 32 #(long-array 32))) (object-array 32) nil)]
    (loop [t 0 ps (vec (repeat N z))]
      (if (= t T) ps
        (let [ps (mapv (fn [v] (let [tok (Object.) v (thaw v tok)]   ; region opens: fresh token
                                 (dotimes [k K] (put! v (.nextInt r (int M)) k tok))
                                 v)) ps)                            ; region closes: token dropped = freeze, O(1)
              a (ancestors-idx r N)]
          (recur (inc t) (mapv #(nth ps (aget a (int %))) (range N))))))))
(defn time-ms [f K] (dotimes [_ 3] (f K))
  (let [xs (sort (for [_ (range 5)] (let [t0 (System/nanoTime)] (f K) (/ (- (System/nanoTime) t0) 1e6))))] (nth xs 2)))
(doseq [K [1 16 256 1024]]
  (println (format "K=%5d  flat+token %8.1f ms" K (time-ms run-flat K))))
