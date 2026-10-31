(ns consolidation.native-pipeline-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [klara.authority :as authority]
            [klara.defs :as d]
            [klara.eval :as ev]
            [ansatz.core :as ansatz]
            [consolidation.checked-pipeline :as pipeline]
            [klara.compile.strict-fold :as fold]
            [klara.compile.staged :as staged]
            [klara.infer-affine-test :as base]
            [klara.stage :as stage]
            [klara.world :as w]
            [proof-staging :as ps]))

(defn requests []
  (let [p (ps/proposals [1 2 3]) domain {:max-count 64 :max-x 100}]
    (mapv #(assoc % :source (:source p) :domain domain :executor :private-array)
          [{:targets [(:numeric p) (:both p)] :steps [{:kind :numeric :coefficients [1 2 3]} {:kind :fusion}]}
           {:targets [(:stream p) (:both p)] :steps [{:kind :fusion} {:kind :numeric :coefficients [1 2 3]}]}
           {:targets [(:stream p)] :steps [{:kind :fusion}]}])))

(deftest pass-orders-share-one-native-lowering
  (doseq [request (requests)]
    (let [cache (stage/make-cache) candidate (pipeline/prepare w/empty-root request)
          info (staged/prepared-info candidate) random (java.util.Random. 2801)]
      (is (= :private-array (:executor info)))
      (is (= 1 (count (get-in info [:native-info :representations]))))
      (is (= :installed (:status (staged/install! cache w/empty-root candidate))))
      (dotimes [_ 24]
        (let [xs (vec (repeatedly (.nextInt random 12) #(long (.nextInt random 100))))]
          (is (= (ps/run-code (:source request) xs)
                 (stage/with-cache cache (ps/run-code (:source request) xs))))))
      (doseq [xs [[] [101] [-1] [1N] [1.5] '(1 2) [Long/MAX_VALUE]]]
        (is (= (base/observe #(ps/run-code (:source request) xs))
               (stage/with-cache cache (base/observe #(ps/run-code (:source request) xs))))))
      (is (pos? (:hits (stage/stats cache))))
      (is (pos? (:fallbacks (stage/stats cache)))))))

(deftest the-native-composition-keeps-each-admission-obligation
  (let [request (first (requests)) cache (stage/make-cache)]
    (staged/install! cache w/empty-root (pipeline/prepare w/empty-root request))
    (let [exe (first (stage/executables cache))]
      (is (nil? (stage/check-certificate exe)))
      (doseq [changed [(assoc-in exe [:lowering :projection] :identity)
                       (assoc-in exe [:native-executable :inference :facts 0 :initial] [99])
                       (assoc exe :private-witness nil)
                       (assoc-in exe [:private-witness :proof] (get-in exe [:private-witness :goal]))
                       (assoc exe :native-executable nil)]]
        (is (= :invalid-checked-chain (stage/check-certificate changed))))
      (let [gs (set (remove #(= :unhandled (first %)) (:guards exe)))
            cert (assoc (:certificate exe) :assumptions gs)
            changed (assoc exe :guards gs :certificate (assoc cert :digest (stage/digest cert)))]
        (is (= :invalid-checked-chain (stage/check-certificate changed))))))
  (let [request (first (requests)) cache (stage/make-cache)]
    (doseq [bad [(assoc-in request [:steps 0 :coefficients] [1 2 4])
                 (assoc-in request [:domain :max-x] Long/MAX_VALUE)
                 (assoc request :executor :unknown)]]
      (is (thrown? clojure.lang.ExceptionInfo (pipeline/prepare w/empty-root bad)))
      (is (empty? (stage/executables cache)))))
  ;; Lowering does not silently fuse map, nor admit effects in a step.
  (is (thrown? clojure.lang.ExceptionInfo
        (fold/prepare w/empty-root (:source (ps/proposals [1 2 3])))))
  (let [source (base/source '(fn [xs]
                              (reduce (fn [a x]
                                        (do (perform :stage/test-tick x)
                                            (assoc a 0 (+ (nth a 0) x)))) [0] xs)))
        ticks (atom [])]
    (with-redefs [ev/reference-handlers (assoc ev/reference-handlers :stage/test-tick
                                            (fn [[x] _] (swap! ticks conj x) nil))]
      (is (= :effect (try (fold/prepare w/empty-root source) :accepted
                         (catch clojure.lang.ExceptionInfo ex (:check (ex-data ex))))))
      (is (empty? @ticks))
      (is (= [6] (base/call source [[1 2 3]])))
      (is (= [1 2 3] @ticks)))))

(deftest count-and-sum-use-the-same-generic-fold-conversion
  (let [src (base/source '(fn [xs]
                           (reduce (fn [a x]
                                     (assoc (assoc a 0 (inc (nth a 0)))
                                            1 (+ (nth a 1) (* x x)))) [0 0] xs)))
        {:keys [candidate lowering info]} (fold/prepare w/empty-root src)
        native (.-executable ^klara.compile.staged.Prepared candidate)]
    (is (= :identity (:projection lowering)))
    (is (= 1 (count (:representations info))))
    (doseq [xs [[] [1 2 3] [-2 4] [3037000500]]]
      (is (= (base/observe #(base/call src [xs]))
             (base/observe #(fold/project lowering ((:run native) xs))))))))

(deftest actual-staged-builders-prepare-in-a-fork-and-publish-after-exit
  (let [world (w/make-world) cache (stage/make-cache)]
    (doseq [path ["experiments/proof_staging/polynomial.klr" "examples/staging/12-native-composition.klr"]]
      (with-open [r (java.io.PushbackReader. (io/reader path))]
        (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} r)))]
          (d/define! world form))))
    (let [root (w/snapshot world)]
      (binding [authority/*store* (authority/new-store)]
        (stage/with-cache cache
          (is (= :installed (:status (d/eval-form root '(refine-native native-request)))))
          (is (= :installed (:status (d/eval-form root '(refine-fold count-sum-code)))))
          (is (= 57 (d/eval-form root '(polynomial-statistic [1 2 3]))))
          (is (= [3 57] (d/eval-form root '(count-sum [1 2 3]))))
          (is (= 99 (d/eval-form root
                      '(handle :dynamic {:host/call (fn [sym f initial xs k] 99)}
                         (count-sum [1 2 3]))))))))
    (is (= 2 (count (stage/executables cache))))))

(deftest native-preparation-and-installation-only-read-captured-proof-environments
  (let [request (first (requests)) before @ansatz/ansatz-env
        index @ansatz/ansatz-instance-index cache (stage/make-cache)
        candidate (pipeline/prepare w/empty-root request)]
    (is (identical? before @ansatz/ansatz-env))
    (is (identical? index @ansatz/ansatz-instance-index))
    (staged/install! cache w/empty-root candidate)
    (is (identical? before @ansatz/ansatz-env))
    (is (identical? index @ansatz/ansatz-instance-index))))

(deftest preparation-does-not-repeat-generation-time-effects
  (let [world (w/make-world) ticks (atom 0) cache (stage/make-cache)]
    (with-open [r (java.io.PushbackReader. (io/reader "experiments/proof_staging/polynomial.klr"))]
      (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} r)))]
        (d/define! world form)))
    (with-redefs [ev/reference-handlers (assoc ev/reference-handlers :stage/generation-observe
                                            (fn [_ _] (swap! ticks inc) nil))]
      (let [p (d/eval-form (w/snapshot world)
                          '(do (perform :stage/generation-observe nil) (polynomial-proposals 1 2 3)))
            request {:source (:source p) :targets [(:numeric p) (:both p)]
                     :steps [{:kind :numeric :coefficients [1 2 3]} {:kind :fusion}]
                     :domain {:max-count 10 :max-x 10} :executor :private-array}]
        (is (= 1 @ticks))
        (staged/install! cache w/empty-root (pipeline/prepare w/empty-root request))
        (is (= 57 (stage/with-cache cache (ps/run-code (:source request) [1 2 3]))))
        (is (= 1 @ticks))))))

(deftest a-mathematical-equality-does-not-license-machine-overflow-motion
  (let [p (ps/proposals [1 0 0])
        request {:source (:source p) :targets [(:numeric p) (:both p)]
                 :steps [{:kind :numeric :coefficients [1 0 0]} {:kind :fusion}]
                 :domain {:max-count 1 :max-x Long/MAX_VALUE} :executor :private-array}
        ;; Deliberately bypass only the mathematical-to-machine domain gate.
        ;; This is a counterexample executor, never installed in a stage cache.
        {:keys [candidate lowering]} (fold/prepare w/empty-root (:both p))
        native (.-executable ^klara.compile.staged.Prepared candidate)]
    (is (= :error (first (base/observe #(ps/run-code (:source p) [Long/MAX_VALUE])))))
    (is (= 1 (fold/project lowering ((:run native) [Long/MAX_VALUE]))))
    (is (= :overflow (try (pipeline/prepare w/empty-root request) :accepted
                         (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))))

(deftest native-worker-host-requirements-survive-mathematical-composition
  (let [request (first (requests)) cache (stage/make-cache) original-vec vec
        array-class (Class/forName "[J")]
    (staged/install! cache w/empty-root (pipeline/prepare w/empty-root request))
    (with-redefs [clojure.core/vec (fn [x] (if (= array-class (class x)) [:wrong] (original-vec x)))]
      (is (= 57 (stage/with-cache cache (ps/run-code (:source request) [1 2 3])))))
    (is (= 1 (:fallbacks (stage/stats cache))))))
