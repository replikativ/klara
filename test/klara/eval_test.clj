(ns klara.eval-test
  "A small corpus of core programs run by T0: closures, letrec, tail
  calls, lexical and nested handlers, multi-shot resumption, exceptions,
  the host boundary, the :world/* reference handlers, specialize."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.core :as c]
            [klara.world :as w]
            [klara.expand :as x]
            [klara.eval :as ev]
            [klara.defs :as d]))

(defn- run [form] (ev/run (x/expand-expr form w/empty-root)))
(defn- err [form] (try (run form) :no-error (catch Throwable t t)))

(deftest core-terms-directly
  (testing "a hand-built term: ((fn [a b] (- a b)) 10 3)"
    (is (= 7 (ev/run (c/app (c/lam 2 (c/prim '- (c/local 1) (c/local 0)))
                            (c/quote* 10) (c/quote* 3))))))
  (testing "letrec: factorial"
    (is (= 120 (ev/run (c/letrec [(c/lam 1 (c/if* (c/prim 'zero? (c/local 0))
                                                   (c/quote* 1)
                                                   (c/prim '* (c/local 0)
                                                           (c/app (c/local 1) (c/prim 'dec (c/local 0))))))]
                                 (c/app (c/local 0) (c/quote* 5)))))))
  (testing "well-formedness rejects scope errors and misplaced effects"
    (is (not (c/wf? (c/lam 1 (c/local 1)))))
    (is (not (c/wf? (c/letrec [(c/quote* 1)] (c/local 0)))))
    (is (not (c/wf? (c/perform nil :user/op))))
    (is (not (c/wf? (c/handle :dynamic {:my/op (c/quote* 1)} (c/quote* 2)))))
    (is (thrown? Exception (ev/run (c/lam 0 (c/local 3)))))))

(deftest closures
  (is (= [11 12] (run '(let [make-adder (fn [n] (fn [x] (+ x n)))
                             a1 (make-adder 1) a2 (make-adder 2)]
                         [(a1 10) (a2 10)]))))
  (is (= [1 2 3] (run '((fn [& xs] (vec xs)) 1 2 3))))
  (is (= 15 (run '(reduce (fn [acc x] (+ acc x)) 0 [1 2 3 4 5])))
      "Klara closures are host IFns"))

(deftest letrec-and-tail-calls
  (is (= [true false] (run '(letfn [(ev? [n] (if (zero? n) true (od? (dec n))))
                                    (od? [n] (if (zero? n) false (ev? (dec n))))]
                              [(ev? 100000) (ev? 100001)])))
      "mutual tail calls in constant space")
  (is (= 499999500000 (run '(loop [i 0 acc 0] (if (< i 1000000) (recur (inc i) (+ acc i)) acc)))))
  (is (= 1000000 (run '((fn count-up [i] (if (< i 1000000) (count-up (inc i)) i)) 0)))
      "self tail call through a named fn")
  (is (= 10 (run '(loop [i 0] (let [j (inc i)] (if (< j 10) (recur j) j)))))
      "recur through a let in tail position, as in Clojure"))

(def state-handler
  '{:get (fn [k] (fn [s] ((k s) s)))
    :put (fn [v k] (fn [s] ((k nil) v)))
    :return (fn [x] (fn [s] [x s]))})

(deftest lexical-handlers
  (testing "state as a function of the store"
    (is (= [42 42] (run `((~'handle [~'st ~state-handler]
                           (~'do (~'perform ~'st :put (~'+ 1 (~'perform ~'st :get)))
                            (~'perform ~'st :get)))
                          41)))))
  (testing "a generator: yield collects, the clause resumes"
    (is (= [[1 2 3] :done]
           (run '(handle [g {:yield (fn [v k] (let [[vs r] (k nil)] [(cons v vs) r]))
                             :return (fn [r] [() r])}]
                   (perform g :yield 1) (perform g :yield 2) (perform g :yield 3) :done)))))
  (testing "abort: a clause that drops k"
    (is (= :aborted (run '(handle [e {:stop (fn [k] :aborted)}] (+ 1 (perform e :stop)))))))
  (testing "multi-shot: resuming twice enumerates"
    (is (= [[true true] [true false] [false true] [false false]]
           (run '(handle [amb {:flip (fn [k] (concat (k true) (k false))) :return (fn [x] [x])}]
                   [(perform amb :flip) (perform amb :flip)]))))))

(deftest nested-handlers
  (testing "perform targets its instance; the inner handler of the same op does not intercept"
    (is (= [:outer-saw 1]
           (run '(handle [outer {:ask (fn [x k] (k [:outer-saw x]))}]
                   (handle [inner {:ask (fn [x k] (k [:inner-saw x]))}]
                     (perform outer :ask 1)))))))
  (testing "inner first, then outer, in one body"
    (is (= [[:i 1] [:o 2]]
           (run '(handle [o {:ask (fn [x k] (k [:o x]))}]
                   (handle [i {:ask (fn [x k] (k [:i x]))}]
                     [(perform i :ask 1) (perform o :ask 2)]))))))
  (testing "deep: the handler stays installed across resumptions"
    (is (= 3 (run '(handle [c {:tick (fn [k] (+ 1 (k nil))) :return (fn [_] 0)}]
                     (perform c :tick) (perform c :tick) (perform c :tick))))))
  (testing "an instance used outside its extent is an error"
    (is (re-find #"unhandled lexical effect"
                 (ex-message (err '(let [h (handle [h {:op (fn [k] (k 1))}] h)]
                                     (perform h :op))))))))

(deftest exceptions
  (is (= {:x 1} (run '(try (throw (ex-info "boom" {:x 1})) (catch Exception e (ex-data e))))))
  (is (= :div0 (run '(try (/ 1 0) (catch ArithmeticException e :div0))))
      "host exceptions become :exn/raise")
  (is (= :outer (run '(try (try (/ 1 0) (catch clojure.lang.ExceptionInfo e :inner))
                           (catch ArithmeticException e :outer))))
      "unmatched catch re-raises to the next dynamic handler")
  (is (= {:x 2} (ex-data (err '(throw (ex-info "uncaught" {:x 2}))))) "uncaught leaves T0")
  (is (= :caught (run '(try (vec (map (fn [x] (if (= x 2) (throw (ex-info "in map" {})) x))
                                      [1 2 3]))
                            (catch Exception e :caught))))
      "exceptions cross the host frame of a callback")
  (is (= 1 (run '(handle [h {:op (fn [k] (k 1))}]
                   (try (perform h :op) (catch Exception e :wrong)))))
      "a dynamic :exn handler does not see lexical effects")
  (is (= :boundary
         (run '(handle [h {:op (fn [k] (k 1))}]
                 (try (vec (map (fn [x] (perform h :op)) [1]))
                      (catch Exception e (if (re-find #"unhandled lexical" (ex-message e))
                                           :boundary :other))))))
      "EF5: a lexical perform behind a host frame is a detected error"))

(deftest dynamic-handlers-override-ambient
  (is (= [:mocked 'clojure.core/slurp]
         (run '(handle :dynamic {:host/call (fn [sym & args] (let [k (last args)] (k [:mocked sym])))}
                 (slurp "/nonexistent")))))
  (is (= 3 (run '(+ 1 2))) "the reference host oracle otherwise"))

(deftest world-reference-handlers
  (let [wo (w/make-world)
        fib (w/fiber wo)]
    (d/define! wo '(def x 1))
    (is (= 0 (d/eval-in fib '(perform :world/version))))
    (d/eval-in fib '(perform :world/define (quote y) 5))
    (is (nil? (d/eval-in fib '(perform :world/resolve (quote y)))) "not before the raise")
    (d/eval-in fib '(perform :world/raise-basis))
    (is (= 5 (d/eval-in fib '(perform :world/resolve (quote y)))))
    (is (= 1 (d/eval-in fib 'x)))))

(deftest specialize-reference-meaning
  (is (= 7 (run '((specialize (fn [a b] (- a b)) 10) 3))))
  (is (= (run '((fn [a b c] [a b c]) 1 2 3))
         (run '((specialize (fn [a b c] [a b c]) 1 2) 3)))
      "s-m-n: run(specialize(p,a),b) = run(p,(a,b))"))
