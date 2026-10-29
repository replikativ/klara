(ns proof-staging-test
  (:require [clojure.test :refer [deftest is]]
            [proof-staging :as p]
            [klara.code :as code]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.fusion.kernel :as k]
            [klara.world :as w]))

(def domain {:max-x 1000000 :max-count 1000})
(defonce family (delay (p/proposals [1 2 3])))
(defonce edges
  (delay (let [{:keys [source numeric stream both]} @family
               n (p/numeric-edge source numeric [1 2 3] domain)
               f (p/fusion-edge numeric both domain)]
           {:numeric n :fusion f :both (p/compose n f)
            :stream (p/fusion-edge source stream domain)})))

(defn observe [thunk]
  (try [:value (thunk)] (catch Throwable e [:exception (class e)])))

(deftest exact-mathematical-endpoints
  (doseq [edge (vals @edges)]
    (is (k/verifies? @p/proof-state (:goal edge) (:proof edge))))
  (let [{:keys [source numeric]} @family
        altered (:numeric (p/proposals [2 2 3]))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not license"
          (p/numeric-edge source altered [1 2 3] domain)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not license"
          (p/numeric-edge source numeric [2 2 3] domain)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not license"
          (p/checked-edge source numeric (k/c "Eq.refl" [k/l1]) domain)))))

(deftest staged-hygiene-and-composition
  (is (= (p/core-term (:source @family))
         (p/core-term (:source (p/proposals [1 2 3])))))
  (is (every? code/closed? (vals @family)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"endpoints do not match"
        (p/compose (:stream @edges) (:fusion @edges))))
  (let [small (p/fusion-edge (:numeric @family) (:both @family)
                             {:max-x 30 :max-count 40})
        composed (p/compose (:numeric @edges) small)]
    (is (= {:max-x 30 :max-count 40} (:domain composed))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed staged code"
        (p/core-term (code/->code (code/var-term (code/fresh 'escaped)))))))

(deftest admitted-values-and-independent-polynomial-oracle
  (let [source (:source @family)]
    (doseq [xs [[] [0] [1 2 3] [1000000] (vec (range 40))
                (vec (repeat 1000 1000000))]]
      (let [expected (reduce +' 0N (map #(+ 1N (*' 2 %) (*' 3 % %)) xs))]
        (is (= expected (p/run-code source xs)))
        (doseq [candidate [:numeric :stream :both]]
          (let [edge (candidate @edges)]
            (is (p/admitted? edge xs))
            (is (= expected (p/run-selected source [edge] xs))))))))
  (doseq [a (range 3) b (range 3) c (range 3)]
    (let [family (p/proposals [a b c])
          n (p/numeric-edge (:source family) (:numeric family) [a b c] domain)
          edge (p/compose n (p/fusion-edge (:numeric family) (:both family) domain))
          xs [0 1 7 31]]
      (is (= (reduce +' 0N (map #(+ a (*' b %) (*' c % %)) xs))
             (p/run-selected (:source family) [edge] xs))))))

(deftest candidate-sum-and-generic-fallback
  (let [source (:source @family) candidates [(:both @edges) (:stream @edges)]]
    (is (identical? (:both @edges) (p/select source candidates [1 2])))
    (is (identical? (:stream @edges) (p/select source (reverse candidates) [1 2])))
    (doseq [xs [[-1] [1N] [1.5] [1/2] [1000001] [Long/MAX_VALUE]
                '(1 2 3) (subvec [0 1 2] 1) (vec (repeat 1001 0))]]
      (is (nil? (p/select source candidates xs)))
      (is (= (observe #(p/run-code source xs))
             (observe #(p/run-selected source candidates xs)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"one source"
          (p/select (:numeric @family) candidates [1])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"checker-issued"
          (p/select source [{:from source :to (:both @family) :domain domain}] [1])))))

(deftest checked-long-is-not-nat
  ;; Integer-valid (x+1)-1 = x changes overflow behavior at MAX_VALUE.
  (let [old (d/eval-form w/empty-root '(code (fn [xs] (- (+ xs 1) 1))))
        new (d/eval-form w/empty-root '(code (fn [xs] xs)))]
    (is (not= (observe #(p/run-code old Long/MAX_VALUE))
              (observe #(p/run-code new Long/MAX_VALUE)))))
  ;; Even multiplying by zero cannot erase overflowing x*x in the source.
  (let [{:keys [source numeric]} (p/proposals [1 0 0])]
    (is (not= (observe #(p/run-code source [Long/MAX_VALUE]))
              (observe #(p/run-code numeric [Long/MAX_VALUE]))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"intermediate may overflow"
          (p/numeric-edge source numeric [1 0 0]
                          {:max-x Long/MAX_VALUE :max-count 1})))
    (let [edge (p/numeric-edge source numeric [1 0 0]
                               {:max-x 3037000499 :max-count 1})]
      (is (= [:value 1] (observe #(p/run-selected source [edge] [3037000499]))))
      (is (nil? (p/select source [edge] [3037000500])))
      (is (= (observe #(p/run-code source [3037000500]))
             (observe #(p/run-selected source [edge] [3037000500]))))))
  (let [{:keys [source numeric]} (p/proposals [Long/MAX_VALUE 0 0])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fold may overflow"
          (p/numeric-edge source numeric [Long/MAX_VALUE 0 0]
                          {:max-x 0 :max-count 2}))))
  (is (thrown? clojure.lang.ExceptionInfo
        (p/numeric-edge (:source @family) (:numeric @family) [1 2 3]
                        {:max-x -1 :max-count 1}))))

(deftest opaque-source-declines
  (doseq [form ['(fn [xs] (reduce + 0 (map (fn [x] (perform :probe x)) xs)))
                '(fn [xs] (reduce + 0 (map (fn [x] (+ offset x)) xs)))
                '(fn [xs] (reduce + 0 (map (fn [x] (- x 1)) xs)))]]
    (is (thrown? clojure.lang.ExceptionInfo
          (p/meaning (d/eval-form w/empty-root (list 'code form)) (k/fvar!))))))

(deftest ambient-admission
  (let [source (:source @family) edge (:both @edges)
        wo (w/make-world)
        chooser (fn [xs] {:selected? (some? (p/select source [edge] xs))
                           :reason (try (p/run-selected source [edge] xs)
                                     (catch clojure.lang.ExceptionInfo ex
                                       (:reason (ex-data ex))))})]
    (d/define! wo (list 'def 'chooser (list 'quote chooser)))
    (is (= {:selected? false :reason :active-handler}
           (d/eval-form (w/snapshot wo)
             '(handle :dynamic {:host/call (fn [sym & as] ((last as) 42))}
                (chooser [1 2])))))
    (doseq [op [:host/call :host/var :exn/raise]]
      (binding [ev/*outer-k* (list (list {:tag :handle :mode :dynamic :clauses {op :handler}}))]
        (is (not (p/admitted? edge [1 2])))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"checker-issued"
          (p/admitted? {:domain domain} [1])))))

(deftest nary-intermediate-overflow
  (let [source (d/eval-form w/empty-root
                 '(code (fn [xs]
                          (reduce + 0
                            (map (fn [x] (+ 1 (+ (* x 0) (* x x 0)))) xs)))))
        target (:numeric (p/proposals [1 0 0]))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"intermediate may overflow"
          (p/numeric-edge source target [1 0 0]
                          {:max-x Long/MAX_VALUE :max-count 1})))))

(deftest reference-host-root-admission
  (let [source (:source @family) edge (:both @edges)
        attempt (fn [] (try (p/run-selected source [edge] [1 2])
                         (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex)))))
        unexpected (fn [& _] (throw (ex-info "changed host helper was invoked" {})))]
    ;; Put the assertions outside with-redefs so the test reporter retains its
    ;; own standard helpers. Guard refusal precedes all traversal/evaluation.
    (is (= :host-roots (with-redefs [clojure.core/map unexpected] (attempt))))
    (is (= :host-roots (with-redefs [clojure.core/reduce unexpected] (attempt))))
    (is (= :host-roots (with-redefs [clojure.core/+ unexpected] (attempt))))
    (let [result (with-redefs [clojure.core/map unexpected]
                   (try (p/checked-edge source (:to edge) (:proof edge) domain)
                     (catch clojure.lang.ExceptionInfo ex (:reason (ex-data ex)))))]
      (is (= :host-roots result)))
    (is (false? (with-redefs [clojure.core/map unexpected] (p/admitted? edge [1]))))))
