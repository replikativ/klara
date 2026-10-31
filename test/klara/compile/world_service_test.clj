(ns klara.compile.world-service-test
  (:require [clojure.test :refer [deftest is]]
            [klara.compile.guest :as guest] [klara.compile.service :as service]
            [klara.compile.loop :as transfer]
            [klara.compile.core :as compiler] [klara.compile.budget :as budget]
            [klara.compile.staged]
            [klara.compile.core-test :refer [observe]] [klara.stage :as stage]
            [klara.world :as world] [klara.defs :as defs] [klara.repl :as repl]))

(def subject '(def f (fn [n] (loop [i n a 1 b 2]
                              (if (> i 0) (recur (dec i) b (+ a b)) a)))))
(def edited-transfer
  (list 'fn '[destinations arguments]
        (list 'let '[tag :edited] (nth guest/transfer-source 2))))
(defn setup []
  (let [w (world/make-world)] (guest/bootstrap! w) (defs/define! w subject) w))

(deftest forked-compiler-definitions-preserve-old-worlds
  (let [w (setup) old (world/fork w) child (world/fork w)
        a (compiler/compile-def old 'f {:mode :baseline})
        _ (defs/define! child (list 'def guest/producer-symbol edited-transfer))
        b (compiler/compile-def child 'f {:mode :baseline})
        cache (stage/make-cache)]
    (is (every? #(= :world-baseline (:producer %)) (:transfer-receipts a)))
    (is (every? #(= :world-stepped (:producer %)) (:transfer-receipts b)))
    (is (every? #(pos? (:service-transitions %)) (:transfer-receipts b)))
    (is (not= (:compiler-reads a) (:compiler-reads b)))
    (is (= #{guest/policy-symbol guest/producer-symbol} (set (map second (:compiler-reads b)))))
    (is (not-any? #(contains? #{guest/policy-symbol guest/producer-symbol} (second %)) (:guards b)))
    (stage/install! cache a)
    (is (= [:value 13 ""] (observe child '(f 5) cache)))
    (is (= [:value 13 ""] (observe old '(f 5) cache)))
    (stage/install! cache b)
    (is (= [:value 13 ""] (observe child '(f 5) cache)))
    (is (zero? (:deopts (stage/stats cache))))
    ;; A later bad compiler edit cannot corrupt an already checked kernel.
    (defs/define! child (list 'def guest/producer-symbol '(fn [a b] {})))
    (is (thrown? clojure.lang.ExceptionInfo (compiler/compile-def child 'f {:mode :baseline})))
    (is (= [:value 13 ""] (observe child '(f 5) cache)))
    (is (= :world-baseline (-> (compiler/compile-def old 'f {:mode :baseline}) :transfer-receipts first :producer)))))

(deftest policy-can-select-a-pure-world-service
  (let [w (setup)]
    (defs/define! w (list 'def 'other-transfer edited-transfer))
    (defs/define! w (list 'def guest/policy-symbol '(fn [request] 'other-transfer)))
    (let [exe (compiler/compile-def w 'f {:mode :baseline})]
      (is (every? #(= 'other-transfer (:producer-symbol %)) (:transfer-receipts exe)))
      (is (every? #(= :world-stepped (:producer %)) (:transfer-receipts exe))))
    (defs/define! w (list 'def guest/policy-symbol '(fn [request] :hosted)))
    (is (= :world-hosted (-> (compiler/compile-def w 'f {:mode :baseline}) :transfer-receipts first :producer)))
    (defs/define! w (list 'def guest/policy-symbol '(fn [request] :decline)))
    (is (= :compiler-policy-declined
           (try (compiler/compile-def w 'f {:mode :baseline}) nil
                (catch clojure.lang.ExceptionInfo e (:reason (ex-data e))))))))

(def touched (atom 0))
(defn touch [] (swap! touched inc))

(deftest edited-services-cannot-bypass-checks-or-bounds
  (doseq [source ['(fn [a b] {:evaluations [] :commits []})
                  '(fn [a b] (klara.compile.world-service-test/touch))
                  '(fn [a b] (loop [] (recur)))]]
    (let [w (setup) b (budget/budget {:work 30000 :emissions 4 :bytes 262144})]
      (defs/define! w (list 'def guest/producer-symbol source))
      (is (thrown? clojure.lang.ExceptionInfo
                   (compiler/compile-def w 'f {:mode :baseline :budget b})))
      (is (pos? (:work (budget/usage b))))
      (is (nil? (:emissions (budget/usage b))))))
  (is (zero? @touched))
  (let [w (setup)]
    (defs/define! w (list 'def guest/policy-symbol '(fn [request] (loop [] (recur)))))
    (is (= :service-transitions
           (try (compiler/compile-def w 'f {:mode :baseline}) nil
                (catch clojure.lang.ExceptionInfo e (:unit (ex-data e))))))))

(deftest service-uses-transitive-definitions-and-disabled-hooks
  (let [w (world/make-world)]
    (defs/define! w '(def helper (fn [x] (+ x 1))))
    (defs/define! w '(def policy (fn [x] (helper x))))
    (let [r (binding [klara.eval/*entry-hook* (fn [& _] (throw (Exception. "native hook ran")))
                      klara.eval/*direct-hook* (fn [& _] (throw (Exception. "native hook ran")))]
              (service/invoke (budget/budget) (world/snapshot w) 'policy [4] 1000))]
      (is (= 5 (:value r)))
      (is (= #{'helper 'policy} (set (map second (:compiler-reads r))))))))

(deftest bootstrap-preserves-existing-edits
  (let [w (setup)]
    (defs/define! w (list 'def guest/policy-symbol '(fn [request] :hosted)))
    (is (empty? (:definitions (guest/bootstrap! w))))
    (is (= :world-hosted (-> (compiler/compile-def w 'f {:mode :baseline}) :transfer-receipts first :producer)))))

(deftest staged-service-can-be-defined-and-prepared-in-the-repl
  (let [s (repl/session)
        loaded (repl/eval-response s (slurp "examples/compat/klara/compiler.cljc"))]
    (is (empty? (:errors loaded)))
    (is (empty? (:errors (repl/eval-response s "(ns scratch) (defn kernel [n] (loop [i n a 1 b 2] (if (> i 0) (recur (dec i) b (+ a b)) a)))"))))
    (let [w (repl/current-world s)
          before (compiler/compile-def w 'scratch/kernel {:mode :baseline})]
      (is (= :world-stepped (-> before :transfer-receipts first :producer)))
      (is (= 'klara.compiler/three (-> before :transfer-receipts first :producer-symbol)))
      (is (pos? (-> before :transfer-receipts first :service-transitions)))
      (is (empty? (:errors (repl/eval-response s "(klara.compiler/prepare-three)"))))
      ;; Installing the generated function for ordinary calls does not bypass
      ;; the compiler service's exact stepping contract.
      (let [after (compiler/compile-def w 'scratch/kernel {:mode :baseline})]
        (is (= :world-stepped (-> after :transfer-receipts first :producer)))
        (is (= (-> before :transfer-receipts first :service-transitions)
               (-> after :transfer-receipts first :service-transitions)))
        (stage/install! (:cache s) after)
        (is (= "13" (repl/eval-string s "(scratch/kernel 5)")))))
    (let [guest (repl/eval-response s "(def kernel-code (code (fn [n] (loop [i n a 1 b 2] (if (> i 0) (recur (dec i) b (+ a b)) a))))) (def generated-kernel (run kernel-code)) (klara.compiler/prepare-code kernel-code) (generated-kernel 5)")]
      (is (empty? (:errors guest)))
      (is (.endsWith ^String (:output guest) "13")))
    ;; The generator describes a family, rather than recognizing the example
    ;; kernel: the same Code program builds multiple admitted transfer arities.
    (doseq [n (range 6)]
      (is (empty? (:errors (repl/eval-response s (str "(def generated (run (klara.compiler/transfer-code " n ")))")))))
      (let [destinations (mapv #(symbol (str "p" %)) (range n))
            arguments (mapv #(hash-map :op :quote :datum (long %)) (range n))
            result (service/invoke (budget/budget) (world/snapshot (repl/current-world s))
                                   'scratch/generated [destinations arguments] 4096)]
        (is (= n (:arity (transfer/check-transfer! destinations arguments (:value result)))))))))
