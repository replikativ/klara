(ns klara.infer-affine-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [klara.affine :as affine]
            [klara.authority :as a]
            [klara.code :as code]
            [klara.compile.affine-erase :as erase]
            [klara.compile.infer-affine :as ia]
            [klara.compile.staged :as staged]
            [klara.core :as c]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.expand :as x]
            [klara.stage :as stage]
            [klara.world :as w]))

(defn example-world []
  (let [world (w/make-world)]
    (with-open [reader (java.io.PushbackReader. (io/reader "examples/staging/08-inferred-affine.klr"))]
      (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} reader)))]
        (d/define! world form))) world))
(defn source [form] (d/eval-form w/empty-root (list 'code form)))
(defn term [source] (code/s->core (code/code-term source)))
(defn call [source args]
  (ev/call-value (ev/run (term source) {:basis w/empty-root}) args))
(defn observe [f]
  (try [:value (f)] (catch Throwable e [:error (class e) (ex-message e)])))

(def counter-form
  '(fn [n] (loop [i 0 acc [0 0]]
             (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc))))

(deftest three-bridges-are-differentially-checked
  (let [random (java.util.Random. 2501)]
    (dotimes [_ 12]
      (let [seed [(long (.nextInt random 30)) (long (.nextInt random 30))]
            world (example-world) root (w/snapshot world)
            src (d/eval-form root (list 'make-counter seed))
            inferred (ia/infer (term src)) target (:owned inferred)
            boxed (eval (:form (erase/erase target (:derivation inferred) {:in-place? false})))
            primitive (eval (:form (erase/erase target (:derivation inferred) {:unbox-parameters? true})))
            cache (stage/make-cache) candidate (ia/prepare root src)]
        (is (= inferred (ia/infer (term src))))
        (is (= :installed (:status (staged/install! cache root candidate))))
        (doseq [args [[0 0] [-1 2] [1 0] [10 4] [20 40]]]
          (let [original (observe #(call src args))]
            (is (= original (observe #(ia/execute-owned inferred args))))
            (is (= original (observe #(apply boxed args))))
            (is (= original (observe #(apply primitive args))))
            (is (= original (stage/with-cache cache (observe #(call src args)))))))))))

(deftest private-copy-preserves-aliases-and-previous-results
  (let [world (example-world) root (w/snapshot world) seed [11 22]
        retained [seed seed] src (d/eval-form root (list 'make-counter (list 'quote seed)))
        cache (stage/make-cache) candidate (ia/prepare root src)]
    (is (= 1 (count (:representations (staged/prepared-info candidate)))))
    (is (empty? (stage/executables cache)))
    (staged/install! cache root candidate)
    (stage/with-cache cache
      (let [snapshot (call src [3 1])]
        (is (= [12 24] snapshot))
        (is (= [14 29] (call src [10 3])))
        (is (= [12 24] snapshot))
        (is (= [[11 22] [11 22]] retained))
        (is (= [11 22] (call src [0 0])))))))

(deftest retained-histories-effects-callbacks-and-input-vectors-decline
  (doseq [form
          ['(fn [n] (loop [i 0 acc [0] history []]
                      (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0))) (conj history acc))
                          [acc history])))
           '(fn [n callback] (loop [i 0 acc [0]]
                               (if (< i n) (recur (inc i) (callback acc)) acc)))
           '(fn [n seed] (loop [i 0 acc seed]
                           (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
           '(fn [n] (loop [i 0 acc [0]]
                      (if (< i n) (do (perform :time/now) (recur (inc i) (assoc acc 0 (inc (nth acc 0))))) acc)))
           '(fn [n] (loop [i 0 acc [0]]
                      (if (< i n) (recur (inc i) (assoc acc 1 (inc (nth acc 1)))) acc)))
           '(fn [n] (loop [i 0 acc [0]]
                      (if (< i n) (recur true (assoc acc 0 (inc (nth acc 0)))) acc)))
           '(fn [n] (loop [i 0 acc [0]]
                      (if (< i n) (recur (inc) (assoc acc 0 (inc (nth acc 0)))) acc)))]]
    (is (= :unsupported-region
           (try (ia/prepare w/empty-root (source form)) :unexpected
                (catch clojure.lang.ExceptionInfo e (:reason (ex-data e)))))))
  ;; This ordinary functional history is semantically meaningful, not dead data.
  (is (= [[3] [[0] [1] [2]]]
         (call (source '(fn [n] (loop [i 0 acc [0] history []]
                                 (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0))) (conj history acc))
                                     [acc history])))) [3]))))

(deftest arithmetic-errors-and-recur-order
  (doseq [form
          ['(fn [n] (loop [i 0 acc [9223372036854775807]]
                      (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
           '(fn [n] (loop [acc [0] i 9223372036854775807]
                      (if (= n 1) (recur (assoc acc 0 (inc (nth acc 0))) (inc i)) acc)))
           '(fn [n] (loop [i 9223372036854775807 acc [0]]
                      (if (= n 1) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
           ;; Parallel scalar assignment, accumulator is the middle argument.
           '(fn [n] (loop [i 0 acc [0 0] a 1 b 2]
                      (if (< i n)
                        (if (< a b)
                          (recur (inc i) (assoc acc 0 (inc (nth acc 0))) b a)
                          (recur (inc i) (assoc acc 1 (inc (nth acc 1))) b a)) acc)))]]
    (let [src (source form) cache (stage/make-cache) inferred (ia/infer (term src))]
      (staged/install! cache w/empty-root (ia/prepare w/empty-root src))
      (doseq [n [0 1 2]]
        (is (= (observe #(call src [n])) (stage/with-cache cache (observe #(call src [n]))))))
      (is (= :left-to-right (get-in inferred [:facts 0 :argument-order]))))))

(deftest guards-fallback-and-certificate-binding
  (let [src (source counter-form) cache (stage/make-cache)]
    (staged/install! cache w/empty-root (ia/prepare w/empty-root src))
    (doseq [n [2.5 3N 5/2 nil :bad]]
      (is (= (observe #(call src [n])) (stage/with-cache cache (observe #(call src [n]))))))
    (is (= 0 (:hits (stage/stats cache))))
    (is (= 5 (:fallbacks (stage/stats cache))))
    (let [exe (first (stage/executables cache))]
      (is (nil? (stage/check-certificate exe)))
      (is (= :invalid-inferred-affine
             (stage/check-certificate (assoc-in exe [:inference :facts 0 :updates] [9])))))
    (with-redefs [c/prims (assoc c/prims 'inc (fn [_] 99))]
      (is (= [99 0] (stage/with-cache cache (call src [1])))))
    (is (= 6 (:fallbacks (stage/stats cache))))
    ;; Backend-only helper roots matter too: changing long-array must not change
    ;; the functional source's vector-valued result.
    (with-redefs [clojure.core/long-array (fn [_] nil)]
      (is (= [1 0] (stage/with-cache cache (call src [1]))))))
  (let [world (example-world) root (w/snapshot world) cache (stage/make-cache)
        src (d/eval-form root '(make-counter [9223372036854775807 0]))]
    (d/define! world (list 'def 'overflow-code (list 'quote src)))
    (d/define! world '(def overflow (run overflow-code)))
    (staged/install! cache root (ia/prepare root src))
    (is (= :caught
           (stage/with-cache cache
             (d/eval-form (w/snapshot world)
               '(handle :dynamic {:exn/raise (fn [e k] :caught)} (overflow 1 1))))))
    (is (= 0 (:hits (stage/stats cache))))))

(deftest caller-compiler-settings-do-not-change-arithmetic-or-bindings
  (let [src (source '(fn [n] (loop [i 0 acc [9223372036854775807]]
                              (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc))))
        cache (stage/make-cache) hostile-ns (create-ns 'klara.infer-affine-test.shadow)]
    (intern hostile-ns 'inc (fn [_] 0))
    (try
      (let [candidate (binding [*unchecked-math* true *ns* hostile-ns]
                        (ia/prepare w/empty-root src))]
        (staged/install! cache w/empty-root candidate)
        (is (= (observe #(call src [1])) (stage/with-cache cache (observe #(call src [1]))))))
      (finally (remove-ns 'klara.infer-affine-test.shadow)))))

(deftest actual-staging-fork-and-persistent-adaptive-policy
  (let [world (example-world) root (w/snapshot world) cache (stage/make-cache)
        store (a/new-store)
        first-batch (binding [a/*store* store]
                      (stage/with-cache cache
                        (d/eval-form root '(operate-counter (counter-controller counter-code 1) [[2 1]] 2))))]
    (is (= [[1 1]] (:values first-batch)))
    (is (false? (get-in first-batch [:controller :attempted])))
    (is (empty? (stage/executables cache)))
    (d/define! world (list 'def 'state (list 'quote (:controller first-batch))))
    (let [result (binding [a/*store* store]
                   (stage/with-cache cache
                     (d/eval-form (w/snapshot world) '(operate-counter state [[3 1] [5 2] [2.5 1]] 2))))]
      (is (= [[1 2] [2 3] [1 2]] (:values result)))
      (is (= 0 (get-in result [:controller :budget])))
      (is (= :installed (get-in result [:controller :publication :status])))
      (is (= 1 (count (stage/executables cache))))
      (is (pos? (:hits (stage/stats cache))))
      (is (pos? (:fallbacks (stage/stats cache))))
      (d/define! world (list 'def 'state (list 'quote (:controller result))))
      (stage/with-cache cache
        (d/eval-form (w/snapshot world) '(operate-counter state [[4 2]] 2)))
      (is (= 1 (count (stage/executables cache)))))
    (stage/clear! cache)
    (is (= [2 3] (stage/with-cache cache (d/eval-form root '(counter 5 2)))))
    (is (every? #(= :settled (:status %)) (vals (:tokens @store)))))
  (let [world (example-world) root (w/snapshot world) cache (stage/make-cache)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"install must follow fork exit"
          (binding [a/*store* (a/new-store)]
            (stage/with-cache cache
              (d/eval-form root '(fork [job (perform :stage/install (perform :stage/prepare-affine counter-code))]
                                  (adopt! job)))))))
    (is (empty? (stage/executables cache)))))
