(ns consolidation.proved-accumulator-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [consolidation.proved-accumulator :as p]
            [consolidation.helper-bridge :as helper]
            [klara.affine :as affine]
            [ansatz.core :as ansatz]
            [klara.compositional-analysis-test :as previous]
            [klara.compile.staged :as staged]
            [klara.core :as c]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.infer-affine-test :as base]
            [klara.authority :as a]
            [klara.stage :as stage]
            [klara.world :as w]))

(def forms
  ['(fn [n] (loop [i 0 acc [0]]
              (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
   '(fn [n] (let [step (fn [a] (let [b a] (assoc b 0 (inc (nth b 0)))))]
              (loop [i 0 acc [0]]
                (let [b acc] (if (< i n) (recur (inc i) (step b)) b)))))
   '(fn [n] (loop [i 0 acc [9223372036854775807]]
              (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
   '(fn [n] (let [unused (fn [a] [a])]
              (loop [i 0 acc [0]]
                (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc))))
   '(fn [n] (let [next-value (fn [a] (let [b a] (inc (nth b 0))))]
              (loop [i 0 acc [0]]
                (if (< i n) (recur (inc i) (assoc acc 0 (next-value acc))) acc))))])

(deftest proof-bearing-native-calls-and-fallback
  (doseq [form forms]
    (let [src (base/source form) cache (stage/make-cache)
          candidate (p/prepare w/empty-root src) info (staged/prepared-info candidate)]
      (is (= :proved-helper-and-private-model (:evidence info)))
      (is (seq (:witness-receipts info)))
      (is (= :installed (:status (staged/install! cache w/empty-root candidate))))
      (doseq [n [0 1 3 100 -1 2.5 3N]]
        (is (= (base/observe #(base/call src [n]))
               (stage/with-cache cache (base/observe #(base/call src [n]))))))
      (is (pos? (:hits (stage/stats cache))))
      (is (pos? (:fallbacks (stage/stats cache)))))))

(deftest exact-model-and-proof-boundaries-are-enforced
  (let [src (base/source (second forms)) cache (stage/make-cache)
        candidate (p/prepare w/empty-root src)]
    (staged/install! cache w/empty-root candidate)
    (let [exe (first (stage/executables cache))]
      (is (nil? (stage/check-certificate exe)))
      (is (= :invalid-proved-accumulator
             (stage/check-certificate (assoc-in exe [:model :seed] 123))))
      (is (= :invalid-proved-accumulator
             (stage/check-certificate
               (assoc-in exe [:kernel-witnesses 0 :proof]
                         (get-in exe [:kernel-witnesses 0 :private-proof])))))
      (is (= :invalid-proved-accumulator
             (stage/check-certificate (dissoc exe :target-witness))))
      (is (= :invalid-proved-accumulator
             (stage/check-certificate
               (assoc-in exe [:target-witness :proof]
                         (get-in exe [:target-witness :private-proof])))))
      ;; Keep the generic certificate envelope internally consistent so this
      ;; failure exercises the proved compiler's required-domain check.
      (let [gs (set (remove #(= [:arg 0 [:long-range 0 Long/MAX_VALUE]] %) (:guards exe)))
            cert (assoc (:certificate exe) :assumptions gs)
            changed (assoc exe :guards gs :certificate (assoc cert :digest (stage/digest cert)))]
        (is (= :invalid-proved-accumulator (stage/check-certificate changed))))))
  (doseq [form ['(fn [n] (loop [i 0 acc [-1]]
                          (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
                '(fn [n] (loop [i 0 acc [0 0]]
                          (if (< i n) (recur (inc i) (assoc acc 0 (inc (nth acc 0)))) acc)))
                '(fn [n] (loop [i 0 acc [0]]
                          (if (< i n) (recur (+ i 2) (assoc acc 0 (inc (nth acc 0)))) acc)))]]
    (is (= :source-model
           (try (p/prepare w/empty-root (base/source form)) :accepted
                (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))))

(deftest actual-world-helpers-and-fork-publication
  (let [wo (w/make-world) cache (stage/make-cache)]
    (d/define! wo (list 'def 'step previous/step))
    (d/define! wo '(def src (code (fn [n] (let [step step]
                                         (loop [i 0 acc [0]]
                                           (if (< i n) (recur (inc i) (step acc)) acc)))))))
    (d/define! wo '(def refine (fn [src]
                                (let [candidate (fork [job (perform :stage/prepare-affine-proved src)]
                                                  (adopt! job))]
                                  (perform :stage/install candidate)))))
    (let [old (w/snapshot wo) src (d/lookup old 'src)
          call (fn [root n]
                 (stage/with-cache cache
                   (ev/call-value (ev/run (previous/term src) {:basis root}) [n])))]
      (is (= :installed (:status (binding [a/*store* (a/new-store)]
                                  (stage/with-cache cache (d/eval-form old '(refine src)))))))
      (is (= [5] (call old 5)))
      (d/define! wo '(def step (fn [a] (let [b a] (assoc b 0 (inc (nth b 0)))))))
      (let [new (w/snapshot wo)]
        (is (= [5] (call new 5)))
        (is (= :installed (:status (staged/install! cache new (p/prepare new src)))))
        (is (= 2 (count (stage/executables cache))))
        (doseq [root [old new old new]] (is (= [5] (call root 5)))))
      (d/define! wo (list 'def 'step previous/wrapped))
      (let [retaining (w/snapshot wo)]
        (is (= :retained-version
               (:check (previous/rejection #(p/prepare retaining src)))))
        (is (= [[0]] (call retaining 1)))
        (is (= [5] (call old 5)))))))

(deftest long-range-admission-is-exact
  (doseq [[pred value expected]
          [[[:long-range 0 Long/MAX_VALUE] 0 true]
           [[:long-range 0 Long/MAX_VALUE] -1 false]
           [[:long-range 0 Long/MAX_VALUE] 1N false]
           [[:long-range 1 0] 1 false]
           [[:long-range 0 2] 2.0 false]]]
    (is (= expected (stage/argument-holds? pred value)))))

(deftest preparation-verification-does-not-switch-the-prover-session
  (let [before @ansatz/ansatz-env index @ansatz/ansatz-instance-index
        src (base/source (second forms)) cache (stage/make-cache)
        candidate (p/prepare w/empty-root src)]
    (is (identical? before @ansatz/ansatz-env))
    (is (identical? index @ansatz/ansatz-instance-index))
    (staged/install! cache w/empty-root candidate)
    (is (identical? before @ansatz/ansatz-env))
    (is (identical? index @ansatz/ansatz-instance-index))))

(deftest staged-profile-policy-requests-but-does-not-license-the-proof
  (let [wo (w/make-world) cache (stage/make-cache)]
    (doseq [path ["examples/staging/10-compositional-accumulator.klr"
                  "examples/staging/11-proof-bearing-accumulator.klr"]]
      (with-open [reader (java.io.PushbackReader. (io/reader path))]
        (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} reader)))]
          (d/define! wo form))))
    (let [root (w/snapshot wo)
          result (binding [a/*store* (a/new-store)]
                   (stage/with-cache cache
                     (d/eval-form root '(operate-with-proof (proof-controller accumulator-code 1) 5 1))))]
      (is (= [5] (:value result)))
      (is (= :installed (get-in result [:controller :publication :status])))
      (is (= 0 (get-in result [:controller :budget])))
      (is (= 1 (count (stage/executables cache))))
      (is (= [7] (stage/with-cache cache (d/eval-form root '(accumulator 7))))))))

(deftest ownership-validity-alone-does-not-prove-the-update-correct
  (let [callback (base/term (base/source '(fn [a] (assoc a 0 (inc (inc (nth a 0)))))))
        owned (p/owned-template 0 callback)]
    (is (some? (affine/check owned)))
    (is (= callback (p/owned-callback owned 0)))
    (is (= :helper-proof
           (try (helper/witness callback) :accepted
                (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex)))))))
  (let [candidate (p/prepare w/empty-root (base/source (first forms)))
        info (staged/prepared-info candidate)
        owned (get-in info [:inference :owned])]
    (is (= :target-model
           (try (p/owned-callback (assoc-in owned [:body :body :body :body :body :name] :own/read) 0)
                :accepted (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))))
