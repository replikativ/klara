(ns klara.snapshot-updates-test
  (:require [clojure.test :refer [deftest is]]
            [klara.compile.infer-affine :as ia]
            [klara.compile.staged :as staged]
            [klara.compile.affine-erase :as erase]
            [klara.affine :as affine]
            [klara.infer-affine-test :as base]
            [klara.stage :as stage]
            [klara.world :as w]))

(def statistic
  '(fn [xs]
     (let [n (count xs)]
       (loop [i 0 acc [0 0]]
         (if (< i n)
           (let [x (nth xs i)]
             (recur (inc i)
                    (assoc (assoc acc 0 (inc (nth acc 0)))
                           1 (+ (nth acc 1) (* x x))))) acc)))))

(deftest input-layouts-and-general-updates-use-the-existing-pipeline
  (let [src (base/source statistic) opts {:parameter-layouts [:long-vector]}
        inferred (ia/infer (base/term src) {} opts)
        candidate (ia/prepare w/empty-root src opts) cache (stage/make-cache)
        boxed (eval (:form (erase/erase (:owned inferred) (:derivation inferred) {:in-place? false})))]
    (is (= 1 (count (:representations (staged/prepared-info candidate)))))
    (is (= :installed (:status (staged/install! cache w/empty-root candidate))))
    (doseq [xs [[] [1] [1 2 3] [-2 3] [3037000500]]]
      (let [original (base/observe #(base/call src [xs]))]
        (is (= original (base/observe #(ia/execute-owned inferred [xs]))))
        (is (= original (base/observe #(boxed xs))))
        (is (= original (stage/with-cache cache (base/observe #(base/call src [xs])))))))
    (doseq [xs [[1N] [1.5] '(1 2 3) nil]]
      (is (= (base/observe #(base/call src [xs]))
             (stage/with-cache cache (base/observe #(base/call src [xs]))))))
    (is (pos? (:hits (stage/stats cache))))
    (is (= 4 (:fallbacks (stage/stats cache))))))

(deftest nested-updates-read-the-old-snapshot-until-all-rhs-are-computed
  ;; A naive chain of array stores changes the second RHS from old slot0=1
  ;; to new slot0=2; this is the essential snapshot obligation.
  (let [src (base/source
              '(fn [n] (loop [i 0 acc [1 0]]
                         (if (< i n)
                           (recur (inc i) (assoc (assoc acc 0 (inc (nth acc 0)))
                                                1 (+ (nth acc 1) (nth acc 0)))) acc))))
        cache (stage/make-cache)]
    (staged/install! cache w/empty-root (ia/prepare w/empty-root src))
    (is (= [4 6] (stage/with-cache cache (base/call src [3]))))
    (doseq [n (range 10)]
      (is (= (base/call src [n]) (stage/with-cache cache (base/call src [n])))))))

(deftest layout-facts-must-hold-on-the-loop-backedge
  ;; Entry x=0 does not license treating x as Long after recur changes it.
  (let [term (base/term
               (base/source '(fn [n]
                               (let [cell (perform :own/alloc [0])]
                                 (do (loop [i 0 x 0]
                                       (if (< i n)
                                         (do (perform :own/update cell (fn [a] (assoc a 0 (+ (nth a 0) x))))
                                             (recur (inc i) 1.5)) nil))
                                     (perform :own/freeze cell))))))
        emitted (erase/erase term (affine/check term) {:unbox-parameters? true})
        f (eval (:form emitted))]
    (is (empty? (:representations emitted)))
    (is (= [1.5] (f 2)))))

(deftest integer-count-is-not-a-boxed-long-result
  ;; Numeric equality would hide this observable representation difference.
  (let [src (base/source '(fn [xs] (loop [i 0 acc [0]]
                                   (if (< i (count xs))
                                     (recur (inc i) (assoc acc 0 (count xs))) acc))))]
    (is (= Integer (class (first (base/call src [[4]])))))
    (is (thrown? clojure.lang.ExceptionInfo
          (ia/prepare w/empty-root src {:parameter-layouts [:long-vector]})))))

(deftest scalar-lets-keep-snapshot-reads-under-their-actual-binders
  (let [src (base/source
              '(fn [n] (loop [i 0 acc [1 0]]
                         (if (< i n)
                           (recur (inc i)
                                  (assoc (assoc acc 0 (let [x (nth acc 0)] (inc x)))
                                         1 (let [x (nth acc 0)]
                                             (let [y (+ x (nth acc 1))] (+ y 0))))) acc))))
        cache (stage/make-cache)
        candidate (ia/prepare w/empty-root src)]
    (is (= 1 (count (:representations (staged/prepared-info candidate)))))
    (staged/install! cache w/empty-root candidate)
    (is (= [4 6] (stage/with-cache cache (base/call src [3]))))
    (doseq [n (range 12)]
      (is (= (base/call src [n]) (stage/with-cache cache (base/call src [n])))))))

(deftest scalar-let-support-does-not-admit-vector-retention-or-unknown-slots
  (doseq [form ['(fn [n] (loop [i 0 acc [0]]
                           (if (< i n) (recur (inc i) (assoc acc 0 (let [alias acc] (vector alias)))) acc)))
                '(fn [n] (loop [i 0 acc [0]]
                           (if (< i n) (recur (inc i) (assoc acc 0 (let [slot 0] (nth acc slot)))) acc)))
                '(fn [n] (loop [i 0 acc [0]]
                           (if (< i n) (recur (inc i) (assoc acc 0 (let [x (nth acc 1)] (inc x)))) acc)))
                '(fn [n] (loop [i 0 acc [0]]
                           (if (< i n) (recur (inc i) (assoc acc 0 (let [size (count acc)] size))) acc)))]]
    (is (thrown? clojure.lang.ExceptionInfo (ia/prepare w/empty-root (base/source form))))))
