(ns klara.affine-test
  (:require [clojure.test :refer [deftest is testing]]
            [klara.authority :as a]
            [klara.affine :as affine]
            [klara.compile.affine-erase :as erase]
            [klara.compile.core :as cc]
            [klara.defs :as defs]
            [klara.stage :as stage]
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
    (doseq [form ['(freeze) '(move) '(read) '(borrow [x 1] x)
                 '(let [o (own 0)] (freeze o) (read o))
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

(def affine-loop
  '(fn [n] (let [o (own [0])]
             (loop [i 0]
               (if (< i n)
                 (do (update! o (fn [v] (assoc v 0 (inc (nth v 0))))) (recur (inc i)))
                 nil))
             (freeze o))))

(deftest affine-erasure-differential
  (doseq [form ['(let [before [1] o (own before)]
                  (let [a (read o)]
                    (update! o conj 2 3)
                    (let [b (borrow [x o] (read x)) p (move o)]
                      [before a b (freeze p)])))
               '(let [o (own [0])]
                  (let [a (read o)]
                    (update! o (fn [v] (assoc v 0 (inc (nth v 0)))))
                    [a (read o) (freeze o)]))
               '(let [o (own 4)] (update! o + 2 3) (freeze o))
               '(let [o (own 4)] (borrow [x o] (borrow [y x] (read y))) (freeze o))]]
    (let [t (x/expand-expr form w/empty-root) d (affine/check t :declared)
          observe (fn [f] (let [v (atom nil) trace (with-out-str (reset! v (f)))] [@v trace]))]
      (binding [a/*store* (a/new-store)]
        (let [checked (observe #(ev/run t))]
          (doseq [in-place? [true false]]
            (let [out (erase/erase t d {:in-place? in-place?})]
              (is (= checked (observe #(eval (:form out)))))
              (is (pos? (:checks-erased out)))))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"derivation"
            (erase/erase t (assoc d :code-id "forged"))))))
  (let [t (x/expand-expr affine-loop w/empty-root) d (affine/check t :declared)
        out (erase/erase t d) f (eval (:form out))]
    (is (= 1 (count (:representations out))))
    (doseq [n [0 1 2 50 1.5]]
      (binding [a/*store* (a/new-store)]
        (is (= (ev/call-value (ev/run t) [n]) (f n)))))))

(deftest affine-compiler-integration
  (let [world (w/make-world) cache (stage/make-cache)]
    (defs/define! world (list 'def 'counter affine-loop))
    (let [exe (cc/compile-def world 'counter)]
      (is (= :affine-erase (get-in exe [:pass-log 0 :pass])))
      (is (= 1 (count (:representations exe))))
      (is (nil? (stage/check-certificate exe)))
      (binding [a/*store* (a/new-store)]
        (is (= [2] ((eval (:form exe)) 1.5))))
      (is (= :invalid-affine-derivation
             (stage/check-certificate (assoc-in exe [:derivation :rules] []))))
      (stage/install! cache exe)
      (stage/with-cache cache
        (binding [a/*store* (a/new-store)]
          (is (= [1000] (defs/eval-form (w/snapshot world) '(counter 1000))))
          (is (= [2] (defs/eval-form (w/snapshot world) '(counter 1.5)))))))))

(deftest conservative-admission-regressions
  (binding [a/*store* (a/new-store)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"general effect"
          (run '(handle :dynamic {:exn/raise (fn [ex k] (+ 1 (k 0)))}
                  (let [o (own 0)] (throw :stop)))))))
  ;; A recursive callback could mutate its captured cell under the update
  ;; lease. It is not a pure function, even if the back edge preserves shares.
  (is (nil? (affine/check
       (x/expand-expr '(let [o (own 0)]
                         (letfn [(again [v] (update! o (fn [x] (again x))))]
                           (again 0))
                         (freeze o)) w/empty-root)))))

(deftest callback-exceptions-and-contexts
  (binding [a/*store* (a/new-store)]
    (is (= :returned
           (run '(let [o (own 1) p (own 2)]
                   (try (borrow [x o] (update! p (fn [_] (/ 1 0))))
                        (catch Exception e (drop! o) (drop! p) :returned))))))
    (is (= [[2]]
           (run '(fork [a (let [o (own 1)]
                           (update! o (fn [v] (+ v 1)))
                           [(freeze o)])]))))))

(deftest seeded-af1-af3-observation-traces
  ;; Ordered persistent snapshots are observable traces in the pure static
  ;; fragment. Compare against an independently functional accumulator.
  (let [random (java.util.Random. 105)]
    (dotimes [_ 40]
      (let [steps (vec (repeatedly (+ 1 (.nextInt random 12)) #(.nextInt random 100)))
            form (list 'fn []
                       (list 'let ['o (list 'own [])]
                         (list 'let
                           (vec (mapcat (fn [i n]
                                          [(symbol (str "write" i)) (list 'update! 'o 'conj n)
                                           (symbol (str "snapshot" i)) (list 'read 'o)]) (range) steps))
                           (list 'vector
                                 (cons 'vector (map #(symbol (str "snapshot" %)) (range (count steps))))
                                 (list 'freeze 'o)))))
            term (x/expand-expr form w/empty-root) d (affine/check term :declared)
            expected [(vec (rest (reductions conj [] steps))) steps]]
        (binding [a/*store* (a/new-store)]
          (is (= expected (ev/call-value (ev/run term) [])))
          (doseq [in-place? [true false]]
            (is (= expected ((eval (:form (erase/erase term d {:in-place? in-place?}))))))))))))

(deftest opaque-inputs-keep-boundary-checks
  (let [events (atom [])
        probe (reify clojure.lang.Counted
                (count [_] (swap! events conj :count) 2))
        term (x/expand-expr '(fn [probe]
                              (let [o (own 0)]
                                (update! o + (count probe)) (freeze o))) w/empty-root)
        d (affine/check term :declared) erased (eval (:form (erase/erase term d)))]
    (is (false? (affine/value? probe)))
    (binding [a/*store* (a/new-store)]
      (is (= 2 (ev/call-value (ev/run term) [probe])))
      (is (= [:count] @events))
      (reset! events [])
      (is (= 2 (erased probe)))
      (is (= [:count] @events)))))

(deftest captured-borrow-cancels-nested-forks
  (binding [a/*store* (a/new-store)]
    (is (= [42]
           (run '(let [o (own [42])]
                   (handle [h {:abort (fn [k] :done)}]
                     (borrow [x o]
                       (fork [a (do (read x) (perform h :abort)) b (read x)])))
                   (freeze o)))))
    (is (= [42]
           (run '(let [o (own [42])]
                   (handle [h {:escape (fn [k] k)}]
                     (borrow [x o]
                       (fork [a (do (read x) (perform h :escape)) b (read x)])))
                   (freeze o)))))))

(deftest lexical-borrow-of-fork-fractions
  (binding [a/*store* (a/new-store)]
    (is (= [[42 42] 42]
           (run '(let [o (own 42)]
                   (let [results (borrow [x o]
                                   (fork [a (borrow [y x] (read y))
                                          b ((fn [^:borrow y] (read y)) x)]))]
                     [results (freeze o)])))))))

(deftest erased-errors-match-t0
  (doseq [form ['(fn [] (let [o (own [9223372036854775807])]
                         (update! o (fn [v] (assoc v 0 (inc (nth v 0)))))
                         (freeze o)))
               '(fn [] (let [o (own 0)] (update! o (fn [v] (/ v 0))) (freeze o)))]]
    (let [term (x/expand-expr form w/empty-root) d (affine/check term :declared)
          observe (fn [f] (try (f) :unexpected-success
                              (catch Throwable e [(class e) (ex-message e)])))
          checked (binding [a/*store* (a/new-store)]
                    (observe #(ev/call-value (ev/run term) [])))]
      (doseq [in-place? [true false]]
        (is (= checked (observe (eval (:form (erase/erase term d {:in-place? in-place?}))))))))))

(deftest non-tail-and-indirect-loop-entry-stay-dynamic
  (doseq [form ['(fn [] (let [o (own 0)]
                         (letfn [(f [n] (if (zero? n) 0 (inc (f (dec n)))))] (f 3))
                         (freeze o)))
               '(fn [] (let [o (own 0)]
                         (letfn [(f [n] n)] (inc (f 3)))
                         (freeze o)))]]
    (is (nil? (affine/check (x/expand-expr form w/empty-root))))))
