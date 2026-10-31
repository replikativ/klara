(ns klara.driver-test
  "Differential observations for the fused driver and explicit CEK driver."
  (:require [clojure.test :refer [deftest is]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [klara.eval :as ev] [klara.expand :as x]
            [klara.world :as w] [klara.authority :as a] [klara.core :as core]))

(def ^:dynamic *trace* nil)
(ev/register-reference-handler! :host/driver-mark
  (fn [[v] _] (swap! *trace* conj v) v))

(defn observe [term reference?]
  (binding [ev/*reference-driver* reference? ev/*entry-hook* nil
            ev/*direct-hook* nil ev/*context-hook* nil
            a/*store* (a/new-store) *trace* (atom [])]
    (let [result (atom nil)
          output (with-out-str
                   (reset! result
                           (try {:value (ev/run term)}
                                (catch Throwable t
                                  {:error [(str (class t)) (ex-message t)
                                           (:klara/error (ex-data t))]}))))]
      (assoc @result :trace @*trace* :output output))))

(def boundary-programs
  ['(let [x 4] [nil false (if nil :bad :nil) (if false :bad :false)
                 ((fn [n] (+ x n)) 3)])
   '(let [x 10]
      (handle [h {:pick (fn [k] [(k 1) (k 2)])}]
        [(perform :host/driver-mark :before) x (perform h :pick)
         (perform :host/driver-mark :after) ((fn [v] v) x)]))
   '(handle [outer {:ask (fn [x k] (k (+ x 10)))}]
      (handle [inner {:ask (fn [x k] (k (+ x 100)))}]
        [(perform outer :ask 1) (perform inner :ask 2)]))
   '(try [(perform :host/driver-mark :before) (/ 1 0) (perform :host/driver-mark :unreachable)]
         (catch ArithmeticException e :caught))
   '(do (perform :host/driver-mark :before) (/ 1 0))
   '(reduce (fn [acc x] (+ acc (perform :host/driver-mark x))) 0 [1 2 3])
   '(handle [h {:op (fn [k] (k 1))}]
      (try (mapv (fn [x] (perform h :op)) [1])
           (catch Exception e :host-boundary)))
   '(let [b (budget 10)] (spend! b 2) (remaining b))
   '(fork [x (do (println "kept") :x) y (do (println "lost") :y)] (adopt! x))
   '(run (code (let [x 4] ((fn [v] (+ v 1)) x))))
   '(let [n 5] (run (code (+ (esc (lift n)) 2))))
   '(try (+ Long/MAX_VALUE 1) (catch ArithmeticException e :overflow))
   '[(+ 1.5 2) (/ 3 2) (+ 1N 2N) (+ 1M 2M) (+) (*) (+ 1 2 3)]
   '(letfn [(even [n] (if (zero? n) true (odd (dec n))))
            (odd [n] (if (zero? n) false (even (dec n))))]
      [(even 100) (odd 101)])])

(deftest control-effects-staging-and-authority-match-reference
  (doseq [form boundary-programs]
    (let [term (x/expand-expr form w/empty-root)]
      (is (= (observe term true) (observe term false)) (pr-str form))))
  (let [term (x/expand-expr (second boundary-programs) w/empty-root)
        result (observe term false)]
    (is (= [:before :after :after] (:trace result)))
    (is (= [[:before 10 1 :after 10] [:before 10 2 :after 10]] (:value result)))))

(defn observable-number []
  (proxy [Number] []
    (intValue [] (swap! *trace* conj :int-value) 4)
    (longValue [] (swap! *trace* conj :long-value) 4)
    (floatValue [] (swap! *trace* conj :float-value) 4.0)
    (doubleValue [] (swap! *trace* conj :double-value) 4.0)))

(deftest primitive-overrides-and-custom-numbers-retain-host-context
  (let [term (x/expand-expr '(+ 1 2) w/empty-root)]
    (with-redefs [core/prims (assoc core/prims '+ (fn [& _] (count ev/*outer-k*)))]
      (is (= (observe term true) (observe term false)))
      (is (= 1 (:value (observe term false))))))
  (let [term (x/expand-expr '(+ (klara.driver-test/observable-number) 1) w/empty-root)
        reference (observe term true) fused (observe term false)]
    (is (= reference fused))
    (is (= 5 (:value fused)))
    (is (seq (:trace fused)))))

(def expressions
  (gen/recursive-gen
    (fn [inner]
      (gen/one-of [(gen/fmap (fn [[a b]] (list '+ a b)) (gen/tuple inner inner))
                   (gen/fmap (fn [[a b]] (list 'let ['x a] (list '+ 'x b))) (gen/tuple inner inner))
                   (gen/fmap (fn [[a b]] (list 'if (list '< a b) a b)) (gen/tuple inner inner))]))
    (gen/choose -20 20)))

(deftest generated-expressions-match-both-drivers-and-clojure
  (let [result
        (tc/quick-check 150
          (prop/for-all [form expressions]
            (let [term (x/expand-expr form w/empty-root)
                  reference (observe term true) fused (observe term false)]
              (and (= reference fused) (= (eval form) (:value fused)))))
          :seed 20261029 :max-size 12)]
    (is (:pass? result) (pr-str result))))
