(ns consolidation.scalar-core-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.env :as env] [ansatz.kernel.name :as nm]
            [consolidation.scalar-core :as scalar] [consolidation.scalar-sum :as sum] [consolidation.scalar-driver :as driver]
            [consolidation.counted-core :as counted]
            [klara.compile.strict-fold :as fold] [klara.code :as code]
            [klara.world :as world] [klara.compile.staged :as staged]
            [klara.core :as c] [klara.eval :as ev] [klara.fusion.kernel :as k]))

(defn evaluate [body args]
  (ev/call-value (ev/run (c/lam (count args) body)) args))
(defn interpret [body args]
  ;; Independent handwritten observer. Kernel-generated JVM model functions
  ;; are not used as a reference oracle.
  (case (:op body)
    :quote (:datum body)
    :local (nth args (- (count args) 1 (:index body)))
    :let (interpret (:body body) (conj args (interpret (:init body) args)))
    :prim (apply (case (:name body) + +' * *') (map #(interpret % args) (:args body)))))

(def bodies
  [(c/prim '+ (c/local 1) (c/local 0))
   (c/prim '+ (c/local 1) (c/prim '* (c/local 0) (c/local 0)))
   (c/let1 (c/prim '* (c/local 0) (c/local 0)) (c/prim '+ (c/local 2) (c/local 0)))
   (c/let1 (c/local 0)
     (c/let1 (c/prim '+ (c/local 0) (c/quote* 1))
       (c/prim '* (c/local 0) (c/prim '+ (c/local 1) (c/local 3)))))])

(deftest scalar-proofs-bind-original-bodies-and-multiple-local-environments
  (let [random (java.util.Random. 3101)]
    (doseq [body bodies]
      (let [witness (scalar/certify-body body [10 10])]
        (is (scalar/verify-body-witness? body [10 10] witness))
        (dotimes [_ 24]
          (let [args [(long (.nextInt random 11)) (long (.nextInt random 11))]]
            (is (= (interpret body args) (evaluate body args)))
            (is (<= (evaluate body args) (:upper witness)))))))))

(deftest literal-representation-binding-and-proof-mutations-are-rejected
  (let [body (c/prim '+ (c/local 1) (c/local 0)) witness (scalar/certify-body body [7 3])]
    (doseq [mutation [(assoc body :name '*) (assoc-in body [:args 0 :index] 0)
                      (c/prim '+ (c/local 1) (c/quote* 3))]]
      (is (not (scalar/verify-body-witness? mutation [7 3] witness))))
    (is (not (scalar/verify-body-witness? body [3 7] witness)))
    (is (not (scalar/verify-body-witness? body [7N 3] witness)))
    (doseq [mutation [(assoc witness :upper 0)
                      (assoc witness :capacity 0)
                      (assoc witness :bound-proof (:bound-goal witness))
                      (assoc witness :checked-proof (:checked-goal witness))
                      (assoc witness :goal-sha256 "wrong")
                      (assoc witness :proof-sha256 "wrong")
                      (assoc witness :source (c/quote* 0))]]
      (is (not (scalar/verify-body-witness? body [7 3] mutation)))))
  (doseq [body [(c/quote* 1N) (c/quote* (int 1)) (c/quote* -1)
                (c/prim '+ (c/local 0) (c/quote* 1) (c/quote* 2))
                (c/prim 'inc (c/local 0))
                (c/perform nil :host/call (c/quote* 'clojure.core/identity) (c/local 0))]]
    (is (thrown? clojure.lang.ExceptionInfo (scalar/certify-body body [10]))))
  (is (thrown? clojure.lang.ExceptionInfo (scalar/certify-body (c/local 1) [10])))
  (is (thrown? clojure.lang.ExceptionInfo (scalar/certify-body (c/prim '+ (c/local 0) (c/quote* 1)) [Long/MAX_VALUE])))
  (is (thrown? clojure.lang.ExceptionInfo
        (scalar/certify-body (c/prim '* (c/prim '* (c/local 0) (c/local 0)) (c/quote* 0)) [4000000000]))))

(deftest independent-generic-proof-receipts-have-no-self-reference
  (doseq [[en names] [[@scalar/proof-state scalar/theorem-names] [@driver/proof-state driver/theorem-names]
                             [@sum/proof-state sum/theorem-names]]
          name names :let [declaration (env/lookup en (nm/from-string name))]]
    (is (env/verifies? en (env/ci-type declaration) (env/ci-value declaration)))
    (is (not (contains? (k/constants-of (env/ci-value declaration)) name)))))

(defn fold-source [body seed prefix]
  (let [xs (if (some? prefix)
             (c/perform nil :host/call (c/quote* 'clojure.core/take) (c/quote* prefix) (c/local 0))
             (c/local 0))]
    (c/lam 1 (c/perform nil :host/call (c/quote* 'clojure.core/reduce) (c/lam 2 body) (c/quote* seed) xs))))

(deftest actual-fold-and-counted-Core-bind-the-indexed-driver-witness
  (doseq [body bodies prefix [nil 0 1 3 20]]
    (let [source (fold-source body 0 prefix) target (:target (fold/lower source))
          witness (counted/witness source target [100 10])
          source-f (ev/run source) target-f (ev/run target)]
      (is (= (c/code-id source) (:source-id witness)))
      (is (= (c/code-id target) (:target-id witness)))
      (is (env/verifies? @driver/proof-state (:goal witness) (:proof witness)))
      (is (env/verifies? @driver/proof-state (:checked-goal witness) (:checked-proof witness)))
      (doseq [xs [[] [1] [1 2 3] [0 1 0 2]]]
        (is (= (ev/call-value source-f [xs]) (first (ev/call-value target-f [xs]))))))))

(deftest changed-counted-protocol-and-step-endpoints-decline
  (let [body (second bodies) source (fold-source body 0 3) target (:target (fold/lower source))
        loop-path [:body :body :body :body :inits 0 :body]
        mutations [(assoc-in target [:body :body :init :datum] 1)
                   (assoc-in target [:body :body :body :init :datum] [1])
                   (assoc-in target (conj loop-path :then :test :args 1 :datum) 4)
                   (assoc-in target (conj loop-path :test :name) '<=)
                   (assoc-in target (conj loop-path :then :then :init :args 1 :index) 0)
                   (assoc-in target (into loop-path [:then :then :body :args 0 :name]) 'dec)
                   (assoc-in target (into loop-path [:then :then :body :args 1 :args 2 :name]) '*)]]
    (doseq [bad mutations]
      (is (thrown? clojure.lang.ExceptionInfo (counted/witness source bad [100 10]))))
    (is (thrown? clojure.lang.ExceptionInfo (counted/witness source target [10])))))


(deftest driver-receipts-keep-the-reachable-safety-premise-explicit
  (let [source (fold-source (second bodies) 0 3) target (:target (fold/lower source))
        receipt (counted/witness source target [100 10])]
    (is (counted/verify-witness? source target [100 10] receipt))
    (is (= :required-not-automatically-discharged (:reachable-safety-premise receipt)))
    (is (contains? (k/constants-of (:checked-goal receipt)) "ScalarRunSafe"))
    (doseq [bad [(assoc receipt :checked-proof (:checked-goal receipt))
                 (assoc receipt :checked-proof-sha256 "wrong")
                 (assoc-in receipt [:scalar-witness :upper] 0)
                 (assoc receipt :target-id "wrong")]]
      (is (not (counted/verify-witness? source target [100 10] bad))))))


(deftest sum-consumer-discharges-the-reachable-Long-invariant
  (doseq [prefix [nil 0 3]]
    (let [source (fold-source (first bodies) 0 prefix) target (:target (fold/lower source))
          receipt (counted/sum-witness source target 64 10)]
      (is (= :discharged-for-sum (:reachable-safety-premise receipt)))
      (is (not (contains? (k/constants-of (:goal receipt)) "ScalarRunSafe")))
      (is (env/verifies? @sum/proof-state (:goal receipt) (:proof receipt)))))
  (let [source (fold-source (first bodies) 0 3) target (:target (fold/lower source))]
    (is (thrown? clojure.lang.ExceptionInfo (counted/sum-witness source target Long/MAX_VALUE 2))))
  (let [source (fold-source (second bodies) 0 3) target (:target (fold/lower source))]
    (is (thrown? clojure.lang.ExceptionInfo (counted/sum-witness source target 64 10)))))


(deftest recognized-scalar-consumers-agree-with-the-existing-native-array-backend
  (doseq [body bodies]
    (let [source (fold-source body 0 3)
          compiled (fold/prepare world/empty-root (code/->code (code/core->s source)))
          native (.-executable ^klara.compile.staged.Prepared (:candidate compiled))
          source-f (ev/run source)]
      (doseq [xs [[] [1] [1 2 3] [1 2 3 4]]]
        (is (= (ev/call-value source-f [xs])
               (fold/project (:lowering compiled) ((:invoke1 native) xs))))))))
