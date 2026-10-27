(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)
(import '[java.util SplittableRandom])
(def N 1000) (def M 1024) (def T 30)
(defn ancestors-idx ^ints [^SplittableRandom r n]
  ;; multinomial-ish: each child picks a uniform ancestor (worst-case duplication)
  (let [a (int-array n)] (dotimes [i n] (aset a i (.nextInt r (int n)))) a))
(defn run-persistent [K]
  (let [r (SplittableRandom. 42)]
    (loop [t 0 ps (vec (repeat N (vec (repeat M 0))))]
      (if (= t T) ps
        (let [ps (mapv (fn [v] (loop [k 0 v v] (if (= k K) v (recur (inc k) (assoc v (.nextInt r (int M)) k))))) ps)
              a (ancestors-idx r N)]
          (recur (inc t) (mapv #(nth ps (aget a (int %))) (range N))))))))
(defn run-transient [K]
  ;; region per step: thaw (transient, O(1) new edit token), K in-place writes, freeze (persistent!) before fork
  (let [r (SplittableRandom. 42)]
    (loop [t 0 ps (vec (repeat N (vec (repeat M 0))))]
      (if (= t T) ps
        (let [ps (mapv (fn [v] (persistent! (loop [k 0 v (transient v)] (if (= k K) v (recur (inc k) (assoc! v (.nextInt r (int M)) k)))))) ps)
              a (ancestors-idx r N)]
          (recur (inc t) (mapv #(nth ps (aget a (int %))) (range N))))))))
(defn run-array [K]
  ;; mutable long[]; fork = clone only on 2nd+ use of an ancestor (what RC=1 buys at array granularity)
  (let [r (SplittableRandom. 42)]
    (loop [t 0 ^objects ps (into-array Object (repeatedly N #(long-array M)))]
      (if (= t T) ps
        (do (dotimes [i N] (let [^longs v (aget ps i)] (dotimes [k K] (aset v (.nextInt r (int M)) (long k)))))
            (let [a (ancestors-idx r N) used (boolean-array N) nps (object-array N)]
              (dotimes [i N] (let [j (aget a i)]
                               (if (aget used j) (aset nps i (aclone ^longs (aget ps j)))
                                   (do (aset used j true) (aset nps i (aget ps j))))))
              (recur (inc t) nps)))))))
(defn time-ms [f K] (dotimes [_ 3] (f K))
  (let [xs (sort (for [_ (range 5)] (let [t0 (System/nanoTime)] (f K) (/ (- (System/nanoTime) t0) 1e6))))] (nth xs 2)))
(doseq [K [1 16 256 1024]]
  (println (format "K=%5d  persistent %8.1f ms  transient-region %8.1f ms  array+clone-on-dup %8.1f ms"
                   K (time-ms run-persistent K) (time-ms run-transient K) (time-ms run-array K))))
