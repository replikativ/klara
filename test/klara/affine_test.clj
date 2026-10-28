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

(deftest owned-surface-and-contracts
  (binding [a/*store* (a/new-store)]
    (is (= [[1] [1 2 3]]
           (run '(let [before [1] o (own before)]
                   (update! o conj 2 3) [before (freeze o)]))))
    (is (= [[42] [42]]
           (run '(let [o (own [42])]
                   (let [v (borrow [x o] (fork [a (read x) b (read x)]))]
                     (drop! o) v)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned"
           (run '(let [o (own 0)] (borrow [x o] (update! x inc))))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"full owned"
           (run '(let [o (own 0)] (fork [a 1 b 2])))))
    (is (= 2 (run '(let [o (own 1)] ((fn [^:own x] (update! x inc)) o) (freeze o)))))
    (is (= [4 4] (run '(let [o (own 4) v ((fn [^:borrow x] (read x)) o)]
                                        [v (freeze o)]))))
    (is (= 4 (run '(let [o (own 4)] ((fn [^:move x] (freeze x)) o)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled"
           (run '(let [o (own 4)] ((fn [^:move x] (freeze x)) o) (read o)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"settled"
           (run '(let [o (own 4)] (freeze o) (freeze o)))))))

(deftest static-affine-fragment
  (let [check (requiring-resolve 'klara.affine/check)]
    (doseq [form ['(let [o (own [1])] (update! o conj 2) (freeze o))
                 '(let [o (own [1]) v (borrow [x o] (read x))] (drop! o) v)
                 '(let [o (own 0) p (move o)] (freeze p))
                 '(fn [n] (let [o (own [0])]
                            (loop [i 0] (if (< i n)
                                          (do (update! o (fn [v] (assoc v 0 (inc (nth v 0)))))
                                              (recur (inc i))) nil))
                            (freeze o)))]]
      (let [term (x/expand-expr form w/empty-root) d (check term :declared)]
        (is (= d (check term :inferred)))
        (is (= d (clojure.edn/read-string (pr-str d))))))
    (doseq [form ['(let [o (own 0)] (freeze o) (read o))
                 '(let [o (own 0) p (move o)] (read o))
                 '(let [o (own 0)] (borrow [x o] (update! x inc)) (freeze o))
                 '(let [o (own 0)] (freeze o) (freeze o))
                 '(let [o (own 0)] (fork [a 1 b 2]))
                 '(let [o (own 0)] o)
                 '(let [o (own 0)] (borrow [x o] x) (freeze o))]]
      (let [term (x/expand-expr form w/empty-root)]
        (is (nil? (check term)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"affine:" (check term :declared)))))
    (is (:klara/affine (meta (:term (x/expand-recorded
          '(defaffine bump [n] (let [o (own n)] (update! o inc) (freeze o))) w/empty-root)))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"affine:"
          (x/expand-recorded '(defaffine bad [] (let [o (own 0)] (freeze o) (read o))) w/empty-root)))))
