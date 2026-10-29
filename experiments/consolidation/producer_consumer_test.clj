(ns consolidation.producer-consumer-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.producer-consumer :as pc]
            [consolidation.producer-model :as model]
            [consolidation.interval :as interval]
            [ansatz.core :as ansatz]
            [consolidation.native-pipeline-test :as previous]
            [consolidation.checked-pipeline :as pipeline]
            [clojure.java.io :as io]
            [klara.compile.staged :as staged]
            [klara.compile.infer-affine :as ia]
            [klara.infer-affine-test :as base]
            [klara.code :as code] [klara.core :as c] [klara.eval :as ev]
            [klara.defs :as d] [klara.authority :as a]
            [klara.stage :as stage] [klara.world :as w]))

(defn setup []
  (let [request (first (previous/requests)) cache (stage/make-cache)
        candidate (pipeline/prepare w/empty-root request)
        closure (ev/run (code/s->core (code/code-term (:source request))) {:basis w/empty-root})]
    (staged/install! cache w/empty-root candidate)
    {:request request :cache cache :consumer (pc/consumer cache closure) :closure closure :candidate candidate}))

(deftest facts-are-bound-to-the-actual-value-and-entail-only-weaker-domains
  (let [xs [1 2] equal-copy (into [] xs) e (stage/refine-argument [:bounded-nat-vector 2 10] xs)]
    (is (stage/evidence-holds? e [:bounded-nat-vector 4 20] xs))
    (is (stage/evidence-holds? e :long-vector xs))
    (is (not (stage/evidence-holds? e [:bounded-nat-vector 1 10] xs)))
    (is (not (stage/evidence-holds? e [:bounded-nat-vector 2 9] xs)))
    (is (not (stage/evidence-holds? e :long-vector equal-copy)))
    (is (not (stage/evidence-holds? {:value xs :predicate :long-vector} :long-vector xs)))))

(deftest actual-producer-transports-facts-without-scanning-the-produced-value
  (let [{:keys [consumer cache]} (setup)
        producer (pc/prepare-producer (base/source '(fn [x] (+ x 1))) 99)
        input (stage/refine-argument [:bounded-nat-vector 64 99] [1 2 3])]
    (with-redefs [stage/argument-holds? (fn [& _] (throw (ex-info "unexpected scan" {})))]
      (let [output (pc/produce producer input)]
        (is (= [2 3 4] (stage/evidence-value output)))
        (is (= [:bounded-nat-vector 3 100] (:predicate (stage/evidence-info output))))
        (is (= 108 (pc/consume consumer output w/empty-root [])))
        (is (= 108 (pc/consume-batch consumer output 20 w/empty-root [])))
        (is (= [1 2 3] (stage/evidence-value input))))
    (is (= 2 (:hits (stage/stats cache)))))
    (is (instance? clojure.lang.IFn$OL (:invoke1 (first (stage/executables cache)))))))

(deftest insufficient-facts-handler-changes-host-changes-and-cache-deletion-fallback
  (let [{:keys [consumer cache]} (setup)
        ;; The actual elements fit, but this evidence does not establish it.
        broad (stage/refine-argument [:bounded-nat-vector 64 101] [1 2 3])
        narrow (stage/refine-argument [:bounded-nat-vector 64 100] [1 2 3])]
    (is (= 57 (pc/consume consumer broad w/empty-root [])))
    (is (= 1 (:fallbacks (stage/stats cache))))
    (is (= 57 (pc/consume consumer narrow w/empty-root [])))
    (let [handled [{:tag :handle :mode :dynamic :clauses {:host/call :test-placeholder}}]
          select (stage/make-evidence-site cache (ev/run (base/term (:source (first (previous/requests))))))]
      ;; Selection only; the real handled invocation is tested below.
      (is (nil? (select narrow w/empty-root handled))))
    (with-redefs [clojure.core/long-array (fn [& _] (throw (ex-info "wrong native path" {})))]
      (is (= 57 (pc/consume consumer narrow w/empty-root []))))
    (let [original-vec vec array-class (Class/forName "[J")]
      (with-redefs [clojure.core/vec (fn [x] (if (= array-class (class x)) [:wrong] (original-vec x)))]
        (is (= 57 (pc/consume consumer narrow w/empty-root [])))))
    (stage/clear! cache)
    (is (= 57 (pc/consume consumer narrow w/empty-root [])))
    (is (= nil (pc/consume-batch consumer nil 0 w/empty-root [])))) )

(deftest prepared-validation-is-reusable-and-binds-the-checker-registry
  (let [{:keys [candidate]} (setup) checked (staged/prevalidate candidate) cache (stage/make-cache)]
    (with-redefs [stage/check-certificate (fn [_] (throw (ex-info "duplicate certificate check" {})))]
      (is (= :installed (:status (staged/install! cache w/empty-root checked))))
      (is (= :installed (:status (staged/install! cache w/empty-root checked)))))
    (let [registry @stage/checkers]
      (try
        (stage/register-checker! :test/changed (constantly nil))
        (is (= :checker-registry-changed
               (try (staged/install! (stage/make-cache) w/empty-root checked) :accepted
                    (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))
        (finally (reset! stage/checkers registry))))))

(deftest world-and-receipt-changes-do-not-get-hidden-by-value-evidence
  (let [world (w/make-world) cache (stage/make-cache)
        _ (d/define! world '(def step (fn [x] (+ x 1))))
        source (d/eval-form (w/snapshot world)
                 '(code (fn [xs] (let [step step]
                                  (let [n (count xs)]
                                    (loop [i 0 acc [0]]
                                      (if (< i n)
                                        (let [x (nth xs i)]
                                          (recur (inc i) (assoc acc 0 (+ (nth acc 0) (step x))))) acc)))))))
        old (w/snapshot world)
        candidate (staged/prevalidate (ia/prepare old source {:parameter-layouts [:long-vector]}))
        evidence (stage/refine-argument [:bounded-nat-vector 2 10] [1 2])
        old-consumer (pc/consumer cache (ev/run (base/term source) {:basis old}))]
    (staged/install! cache old candidate)
    (is (= [5] (pc/consume old-consumer evidence old [])))
    (d/define! world '(def step (fn [x] (* x 10))))
    (let [new (w/snapshot world)
          new-consumer (pc/consumer cache (ev/run (base/term source) {:basis new}))]
      (is (= :stale-world (:reason (staged/install! (stage/make-cache) new candidate))))
      (is (= [30] (pc/consume new-consumer evidence new [])))
      (is (= [5] (pc/consume old-consumer evidence old []))))
    (let [bad (klara.compile.staged.Prepared.
                (.-source ^klara.compile.staged.Prepared candidate)
                (assoc (.-executable ^klara.compile.staged.Prepared candidate) :run (constantly :wrong))
                (.-info ^klara.compile.staged.Prepared candidate))]
      (is (= :validation-mismatch
             (try (staged/install! cache old bad) :accepted
                  (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex)))))))))

(deftest old-value-facts-survive-producer-changes-without-licensing-new-values
  (let [input (stage/refine-argument [:bounded-nat-vector 3 10] [1 2 3])
        first-producer (pc/prepare-producer (base/source '(fn [x] (+ x 1))) 10)
        second-producer (pc/prepare-producer (base/source '(fn [x] (* x 10))) 10)
        old (pc/produce first-producer input) new (pc/produce second-producer input)]
    (is (stage/evidence-holds? old [:bounded-nat-vector 3 11] (stage/evidence-value old)))
    (is (not (stage/evidence-holds? old [:bounded-nat-vector 3 11] (stage/evidence-value new))))
    (is (not (stage/evidence-holds? new [:bounded-nat-vector 3 11] (stage/evidence-value new))))
    (with-redefs [c/prims (assoc c/prims '+ (constantly 999))]
      (is (= :producer-host-root
             (try (pc/prepare-producer (base/source '(fn [x] (+ x 1))) 10) :accepted
                  (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))
      (is (= :producer-host-root
             (try (pc/produce first-producer input) :accepted
                  (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))
      (is (stage/evidence-holds? old [:bounded-nat-vector 3 11] (stage/evidence-value old))))))

(deftest actual-staging-and-active-handlers-use-the-current-context
  (let [world (w/make-world) cache (stage/make-cache)]
    (doseq [path ["experiments/proof_staging/polynomial.klr"
                  "examples/staging/12-native-composition.klr" "examples/staging/13-producer-consumer.klr"]]
      (with-open [r (java.io.PushbackReader. (io/reader path))]
        (doseq [form (take-while #(not= ::end %) (repeatedly #(read {:eof ::end} r)))]
          (d/define! world form))))
    (let [root (w/snapshot world)]
      (binding [a/*store* (a/new-store)]
        (stage/with-cache cache
          (is (= :installed (:status (d/eval-form root '(refine-native native-request)))))
          (is (= 108 (d/eval-form root '(produced-statistic [1 2 3] 5))))
          (is (= 30806 (d/eval-form root '(produced-statistic [100] 1))))
          (is (= nil (d/eval-form root '(produced-statistic [1 2 3] -1))))
          (is (= 108 (d/eval-form root '(produced-statistic [1 2 3] 0.5))))
          (is (= 99 (d/eval-form root
                      '(handle :dynamic {:host/call (fn [& args] 99)}
                         (produced-statistic [1 2 3] 5))))))))))

(deftest multiple-producers-and-consumer-alternatives-compose-their-domains
  (let [{:keys [consumer cache request]} (setup)
        input (stage/refine-argument [:bounded-nat-vector 64 99] [1 2 3])
        shift (pc/prepare-producer (base/source '(fn [x] (+ x 1))) 99)
        square (pc/prepare-producer (base/source '(fn [x] (* x x))) 100)
        output (pc/produce square (pc/produce shift input))]
    (is (= [4 9 16] (stage/evidence-value output)))
    (is (= 1120 (pc/consume consumer output w/empty-root [])))
    (is (= 1 (:fallbacks (stage/stats cache))))
    (staged/install! cache w/empty-root
                     (pipeline/prepare w/empty-root (assoc-in request [:domain :max-x] 10000)))
    (is (= 1120 (pc/consume consumer output w/empty-root [])))
    (is (= 1 (:hits (stage/stats cache))))))

(deftest producer-proof-checking-and-runtime-do-not-use-statistics-as-facts
  (let [source (base/source '(fn [x] (* x 10)))
        bounds (interval/certify (:body (base/term source)) 10 Long/MAX_VALUE)
        before @ansatz/ansatz-env index @ansatz/ansatz-instance-index]
    (is (= :producer-proof
           (try (model/witness (assoc bounds :upper 99) 10) :accepted
                (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex))))))
    (let [producer (pc/prepare-producer source 10)
          input (stage/refine-argument [:bounded-nat-vector 1 10] [10])]
      (is (= [100] (stage/evidence-value (pc/produce producer input))))
      (is (identical? before @ansatz/ansatz-env))
      (is (identical? index @ansatz/ansatz-instance-index))))
  (let [realized (atom false) xs (lazy-seq (reset! realized true) [1])]
    (is (nil? (stage/refine-argument [:bounded-nat-vector 10 10] xs)))
    (is (false? @realized)))
  (doseq [xs [[-1] [1N] [1.5]]]
    (is (nil? (stage/refine-argument [:bounded-nat-vector 10 10] xs)))))

(deftest materialization-preserves-retained-input-and-prior-output-versions
  (let [xs (mapv #(long (mod % 10)) (range 128)) retained [xs xs]
        evidence (stage/refine-argument [:bounded-nat-vector 128 9] xs)
        producer (pc/prepare-producer (base/source '(fn [x] (+ x 1))) 9)
        next-producer (pc/prepare-producer (base/source '(fn [x] (+ x 1))) 10)
        first-output (pc/produce producer evidence)
        second-output (pc/produce next-producer first-output)]
    (is (= xs (first retained) (second retained) (stage/evidence-value evidence)))
    (is (= (mapv inc xs) (stage/evidence-value first-output)))
    (is (= (mapv #(+ % 2) xs) (stage/evidence-value second-output)))))
