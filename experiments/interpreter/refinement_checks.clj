(ns interpreter.refinement-checks
  "Executable storage/failure obligations, not a machine simulation theorem."
  (:require [clojure.test :as test :refer [deftest is]]
            [clojure.java.io :as io] [clojure.pprint :as pp]
            [interpreter.bridge :as b] [interpreter.activation :as a]
            [interpreter.bridge-checks :as checks] [interpreter.mutable-checks :as cases]
            [klara.expand :as x] [klara.world :as w] [klara.eval :as ev]
            [klara.core :as core])
  (:import [java.util IdentityHashMap ArrayList]))

(defn- buffers
  "Enumerate currently active writable storage. Sealed capture arrays, source
   nodes and immutable plans are deliberately excluded from this ownership set."
  [capsule activation?]
  (let [{:keys [registers frames scratch]} (:machine @(:life capsule))
        ^objects r registers ^ArrayList frames frames
        depth (long (aget r 4))
        out (IdentityHashMap.)]
    (doseq [v (concat [r frames (aget r (if activation? 1 2))]
                     (when scratch [scratch (aget ^objects scratch 0)])
                     (mapcat (fn [i]
                               (let [^objects f (.get frames i)]
                                 (if activation? [f (aget f 1)] [f (aget f 2) (aget f 4)])))
                             (range depth)))]
      (.put out v true))
    out))

(defn- view [c]
  (checks/signature (:state (b/transfer! (b/thaw (b/freeze c)))) w/empty-root))

(defn- observation [f]
  (try {:value (f)}
       (catch ArithmeticException ex {:error :arithmetic :message (.getMessage ex)})))

(deftest thawed-executions-have-disjoint-active-writable-storage
  (doseq [[prepare activation?] [[b/prepare false] [a/prepare true]]
          form [(nth cases/programs 0) (nth cases/programs 1) (nth cases/programs 3)]
          fuel [0 7 23 59]]
    (let [artifact (prepare (x/expand-expr form w/empty-root))
          original (b/start artifact [8]) _ (b/advance! original fuel)
          snapshot (b/freeze original) left (b/thaw snapshot) right (b/thaw snapshot)
          right-before (view right)
          owned (mapv #(buffers % activation?) [original left right])]
      (doseq [[i j] [[0 1] [0 2] [1 2]]]
        (is (not-any? #(.containsKey ^IdentityHashMap (owned j) %) (.keySet ^IdentityHashMap (owned i)))))
      (b/advance! left 19)
      (is (= right-before (view right) (view (b/thaw snapshot))))
      (is (= ((ev/run (:source artifact)) 8)
             (b/resume! (b/transfer! left))
             (b/resume! (b/transfer! right))
             (b/resume! (b/transfer! original)))))))

(deftest failure-order-and-recovery-agree-at-every-pre-failure-pause
  (doseq [prepare [b/prepare a/prepare]
          [form input] [['(fn [n] (+ (+ 9223372036854775807 1) (/ 1 0))) 0]
                        ['(fn [n] (+ (/ 1 0) (+ 9223372036854775807 1))) 0]
                        ['(fn [n] (let [x (+ n 1)] (* x 0))) Long/MAX_VALUE]
                        ['(fn [n] (if false (/ 1 0) (+ n 1))) 0]]]
    (let [artifact (prepare (x/expand-expr form w/empty-root))
          expected (observation #((ev/run (:source artifact)) input))
          c (b/start artifact [input])]
      (loop [steps 0]
        (assert (< steps 200) "test exceeded the declared transition bound")
        (let [snapshot (b/freeze c)]
          (doseq [reference? [true false]]
            (is (= expected (observation #(b/resume! (b/transfer! (b/thaw snapshot)) reference?)))))
          (let [result (observation #(b/advance! c 1))]
            (cond
              (:error result) (do (is (= expected result))
                                  (is (= :failed (b/status c)))
                                  (is (thrown? clojure.lang.ExceptionInfo (b/freeze c))))
              (= :done (:value result)) (is (= expected (observation #(b/result! c))))
              :else (recur (inc steps)))))))))

(defn -main [& _]
  (require 'consolidation.scalar-block-test 'consolidation.counted-loop-test 'interpreter.activation-checks)
  (let [result (test/run-tests 'interpreter.mutable-checks 'interpreter.bridge-checks
                               'interpreter.activation-checks 'interpreter.refinement-checks
                               'consolidation.scalar-block-test 'consolidation.counted-loop-test)
        sources (cons "deps.edn"
                      (mapcat (fn [directory]
                                (map str (filter #(and (.isFile %) (.endsWith (str %) ".clj"))
                                                 (file-seq (io/file directory)))))
                              ["src" "test" "experiments/consolidation" "experiments/interpreter"]))
        report {:tests result :java (System/getProperty "java.runtime.version")
                :clojure (clojure-version)
                :source-sha256 (into (sorted-map) (map (fn [p] [p (core/sha256 (slurp p))]) sources))
                :claims [:kernel-checked-per-source-scalar-block-refinement
                         :kernel-checked-composition-with-scalar-CEK
                         :kernel-checked-counted-update-composition
                         :executable-private-storage-and-recovery-checks]
                :not-proved [:full-T0 :hosted-decoder :JVM-emission :general-world-and-authority-simulation]}
        output "target/runtime-refinement/report.edn"]
    (io/make-parents output)
    (spit output (with-out-str (pp/pprint report)))
    (when (pos? (+ (:fail result) (:error result)))
      (throw (ex-info "Runtime refinement checks failed" report)))
    (println :report output))
  (shutdown-agents))
