(ns klara.compile.generated-test
  "Bounded, well-scoped program generation, with shrinking and fixed seeds.
  T0 supplies values/errors; a Counted probe supplies ordered effect traces."
  (:require [clojure.test :refer [deftest is]]
            [clojure.test.check :as tc] [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [klara.compile.core-test :refer [setup observe]]
            [klara.compile.core :as cc] [klara.stage :as stage]))

(defn expr [vars depth]
  (let [leaf (gen/one-of [(gen/elements (into vars ['(count (first probe)) '(count (second probe))])) (gen/choose -4 4)])]
    (if (zero? depth) leaf
        (let [sub #(expr vars (dec depth))]
          (gen/frequency
           [[4 leaf]
            [3 (gen/let [op (gen/elements '[+ - * /]) a (sub) b (sub)] (list op a b))]
            [2 (gen/let [a (sub) b (sub) d (sub)] (list 'if (list '> a 0) b d))]
            [2 (gen/let [a (sub) b (expr (conj vars 'local) (dec depth))]
                 (list 'let ['local a] b))]
            [2 (gen/let [a (sub) b (sub) i (gen/elements [0 1])]
                 (list 'let ['v [a b]] (list 'nth 'v i)))]
            [2 (gen/let [a (sub) b (sub) k (gen/elements [:a :b])]
                 (list 'let ['m {:a a :b b}] (list 'get 'm k)))]
            [2 (gen/let [body (expr (conj vars 'arg) (dec depth)) a (sub) b (sub)]
                 (list 'let ['f (list 'fn ['arg] body)] (list '+ (list 'f a) (list 'f b))))]
            [1 (gen/let [a (sub) abort? gen/boolean]
                 (list 'handle ['h {:op (if abort? '(fn [x k] (+ x 1)) '(fn [x k] (k (+ x 1))))}]
                       (list '+ (list 'perform 'h :op a) 2)))]])))))

(def accepted-program
  (gen/let [body (expr ['n] 3) kind (gen/choose 0 3) bound (gen/choose 0 6)]
    (list 'fn ['n 'probe]
          (list 'let ['traced '(count (first probe))]
                (case kind
                  0 body
                  1 (list 'let ['y body] '(+ y 1))
                  2 (list 'loop ['i bound 'acc 0]
                          (list 'if '(> i 0) (list 'recur '(dec i) (list '+ 'acc body)) 'acc))
                  3 (list 'let ['e '(evidence 1) 'paid '(spend! e 1/4) 'y body]
                          '(+ y (remaining e))))))))

(def rejected-program
  (gen/let [body (expr ['n] 2) kind (gen/choose 0 4)]
    (list 'fn ['n 'probe]
          (case kind
            0 (list 'do '(println n) body)
            1 (list 'fn [] body)
            2 (list 'handle ['h {:op '(fn [x k] (+ (k x) (k x)))}]
                    (list '+ body '(perform h :op n)))
            3 (list 'handle :dynamic {:exn/raise '(fn [x k] (k 0))} body)
            4 (list 'loop ['i 2] (list 'if '(> i 0) '(+ 1 (recur (dec i))) body))))))

(defn observations [world form cache trace]
  (reset! trace [])
  [(observe world form cache) @trace])

(defn probes [trace]
  (mapv (fn [label] (reify clojure.lang.Counted
                     (count [_] (swap! trace conj label) 1))) [:first :second]))

(defn equivalent? [program]
  (let [world (setup program) cache (stage/make-cache)
        exe (cc/compile-def world 'f) trace (atom [])
        probe (probes trace)]
    (stage/install! cache exe)
    (and
     (every? (fn [n]
               (let [form (list 'f n (list 'quote probe))]
                 (= (observations world form (stage/make-cache) trace)
                    (observations world form cache trace))))
             [0 1 -2 1.5 :bad Long/MAX_VALUE])
     (pos? (:hits (stage/stats cache)))
     (let [form (list 'f 3 (list 'quote probe)) before (observations world form cache trace)]
       (stage/clear! cache)
       (= before (observations world form cache trace))))))

(deftest generated-accepted-differential
  (let [result (tc/quick-check 160 (prop/for-all [p accepted-program] (equivalent? p))
                               :seed 90210 :max-size 20)]
    (is (:pass? result) (pr-str result))))

(deftest generated-rejections-leave-t0
  (let [result (tc/quick-check
                50 (prop/for-all [p rejected-program]
                     (let [world (setup p) cache (stage/make-cache)
                           rejected? (try (cc/compile-def world 'f) false
                                          (catch clojure.lang.ExceptionInfo e
                                            (= :compile (:klara/error (ex-data e)))))
                           trace (atom [])
                           probe (probes trace)]
                       (and rejected? (empty? (stage/executables cache))
                            (every? (fn [n]
                                      (let [call (list 'f n (list 'quote probe))
                                            ;; Observe an escaping closure by calling it.
                                            form (if (= 'fn (first (nth p 2))) (list call) call)]
                                        (= (observations world form (stage/make-cache) trace)
                                           (observations world form cache trace)))) [-1 0 2]))))
                :seed 901 :max-size 15)]
    (is (:pass? result) (pr-str result))))
