(ns klara.affine-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.authority :as a]
            [klara.expand :as x]
            [klara.eval :as ev]
            [klara.world :as w]))

(defn run [form] (ev/run (x/expand-expr form w/empty-root)))

(deftest owned-effects-admission
  (binding [a/*store* (a/new-store)]
    (is (= [2] (run '(let [o (perform :own/alloc [1])]
                            (perform :own/update o conj 2)
                            (rest (perform :own/freeze o))))))
    (is (= 7 (run '(handle [h {:get (fn [k] (k 7))}]
                    (let [o (perform :own/alloc 0)]
                      (let [v (perform h :get)] (perform :own/drop o) v))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"general effect"
          (run '(handle [h {:get (fn [k] (+ 1 (k 7)))}]
                  (let [o (perform :own/alloc 0)] (perform h :get))))))))

(deftest borrow-machine-cleanup
  (doseq [body ['(read x) '(throw :failed)
               '(perform h :abort) '(perform h :escape)]]
    (binding [a/*store* (a/new-store)]
      (let [token (a/op! :own/alloc [42] [])]
        ;; Exercise with a token supplied as a literal (host test only).
        (let [form (list 'handle ['h {:abort '(fn [k] :done) :escape '(fn [k] k)}]
                         (list 'perform :own/borrow (list 'quote token) (list 'fn ['x]
                                 (if (= body '(read x)) '(perform :own/read x) body))))
              result (try (run form) (catch Exception _ :failed))]
          (is (= 1 (get-in (a/state token) [:payload :share])))
          (when (instance? klara.eval.Cont result)
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"outlived"
                                  (ev/call-value result [0])))))
        (a/op! :own/drop [token] [])))))
