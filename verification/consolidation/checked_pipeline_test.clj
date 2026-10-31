(ns consolidation.checked-pipeline-test
  (:require [clojure.test :refer [deftest is]]
            [consolidation.checked-pipeline :as pipeline]
            [proof-staging :as ps]
            [klara.authority :as a]
            [klara.compile.staged :as staged]
            [klara.defs :as d]
            [klara.stage :as stage]
            [klara.world :as w]))

(defn request []
  (let [p (ps/proposals [1 2 3])]
    {:source (:source p) :targets [(:numeric p) (:both p)]
     :steps [{:kind :numeric :coefficients [1 2 3]} {:kind :fusion}]
     :domain {:max-count 10 :max-x 10}}))

(deftest actual-fork-install-and-guarded-invocation
  (let [wo (w/make-world) cache (stage/make-cache) req (request)]
    (d/define! wo (list 'def 'request (list 'quote req)))
    (d/define! wo '(def f (run (:source request))))
    (d/define! wo '(def refine (fn [r]
                                (let [candidate (fork [job (perform :stage/prepare-checked r)]
                                                  (adopt! job))]
                                  (perform :stage/install candidate)))))
    (let [root (w/snapshot wo) expected (d/eval-form root '(f [1 2 3]))]
      (is (empty? (stage/executables cache)))
      (is (= :installed (:status (binding [a/*store* (a/new-store)]
                                  (stage/with-cache cache (d/eval-form root '(refine request)))))))
      (is (= expected (stage/with-cache cache (d/eval-form root '(f [1 2 3])))))
      (is (pos? (:hits (stage/stats cache))))
      (doseq [xs [[11] [-1] [1.5] [1N] (vec (range 11))]]
        (is (= (d/eval-form root (list 'f (list 'quote xs)))
               (stage/with-cache cache (d/eval-form root (list 'f (list 'quote xs)))))))
      (is (= 5 (:fallbacks (stage/stats cache)))))))

(deftest failed-proof-does-not-publish
  (let [req (request) cache (stage/make-cache) wo (w/make-world)
        bad (assoc-in req [:steps 0 :coefficients] [1 2 4])]
    (is (thrown? clojure.lang.ExceptionInfo (pipeline/prepare w/empty-root bad)))
    (d/define! wo (list 'def 'request (list 'quote bad)))
    (is (= :declined (:status (stage/with-cache cache
                               (d/eval-form (w/snapshot wo)
                                 '(perform :stage/install (perform :stage/prepare-checked request)))))))
    (is (empty? (stage/executables cache))))
  (let [req (request) cache (stage/make-cache)
        candidate (pipeline/prepare w/empty-root req)]
    (staged/install! cache w/empty-root candidate)
    (let [exe (first (stage/executables cache))]
      (is (nil? (stage/check-certificate exe)))
      (is (= :invalid-checked-chain
             (stage/check-certificate (assoc exe :target (:generic exe))))))))

(deftest domain-checking-is-inert-and-fail-closed
  (let [ran (atom false) lazy-input (lazy-seq (reset! ran true) (list 1))]
    (is (false? (stage/argument-holds? [:bounded-nat-vector 10 10] lazy-input)))
    (is (false? @ran))
    (is (false? (stage/argument-holds? [:bounded-nat-vector -1 10] [1])))))
