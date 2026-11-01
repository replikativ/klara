(ns klara.staged-test
  "The staged interpreter (design/08-staged-jit.md): as an interpreter it
  agrees with the machine; with everything dynamic its residual is the
  reference again, which the kernel admits (L4.jit.staged)."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [klara.formal.gen :as gen]
            [klara.host.api :as k]
            [klara.lang.expand :as ex]))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(deftest the-generator-is-an-interpreter   ; L4.jit.staged
  (let [s (session)]
    (is (= (vec (repeat 6 true))
           (k/eval-string s "(ns st (:require [klara.jit.staged :as staged] [klara.compiler :as compiler]))
             (defn fib [n] (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
             (defn sum-to [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc i)) acc)))
             (defn adder [x] (fn [y] (+ x y)))
             (def k 10)
             (defn scaled [x] (let [y (* x k)] (do (str y) (+ y 1))))
             (defn pick [m] (if (contains? m :a) (:a m) [m k]))
             (defn nested [n] (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc (loop [j 0 s 0] (if (< j i) (recur (inc j) (+ s j)) s)))) acc)))
             (defn run [q & args] (apply staged/interpret (compiler/reference q) args))
             [(= (run 'st/fib 15) (fib 15))
              (= (run 'st/sum-to 100) (sum-to 100))
              (= ((run 'st/adder 3) 4) 7)
              (= (run 'st/scaled 4) (scaled 4))
              (= (run 'st/pick {:b 1}) (pick {:b 1}))
              (= (run 'st/nested 6) (nested 6))]")))))

(defn- defined-functions [src]
  (let [r (clojure.lang.LineNumberingPushbackReader. (java.io.StringReader. src))]
    (loop [out []]
      (let [f (ex/read-all r 'user)]
        (if (ex/eof? f) out (recur (if (and (seq? f) (= 'defn (first f))) (conj out (second f)) out)))))))

(def seeds (or (some-> (System/getenv "KLARA_STRESS_SEEDS") parse-long) 100))

(deftest residuals-are-the-reference   ; L4.jit.staged
  (testing "generated programs: every definition's all-dynamic residual is admitted by the kernel"
    (let [results (for [seed (range seeds)
                        :let [src (gen/program seed)
                              s (session)
                              _ (try (k/eval-string s src) (catch Exception _ nil))
                              _ (k/eval-string s "(require '[klara.jit.staged] '[klara.compiler])")]
                        f (defined-functions src)]
                    (let [o (k/eval-string s (str "(klara.compiler/prepare (klara.compiler/reference 'gen/" f ")"
                                                  " {:recipe (fn [r] (klara.jit.staged/residual r)) :name 'gen/" f "})"))]
                      {:seed seed :f f :status (:status o) :rule (:rule o) :message (:message o)}))
          ;; constructs the generator does not interpret yet (P7.5) are skipped
          pending? #(some-> (:message %) (str/includes? "not interpreted yet"))
          ;; admitted by the checker but outside what the backend compiles: as the reference
          bad (remove #(or (= :ready (:status %)) (= :L4.lower.subset (:rule %)) (pending? %)) results)]
      (is (empty? (take 3 bad)) (pr-str (take 3 bad)))
      (is (< (count (filter pending? results)) (count results))))))

(deftest known-calls-are-unfolded   ; L4.jit.staged
  (testing "an interpreter called on a known program: the residual is the program's code, admitted by the kernel"
    (let [s (session)]
      (is (= [:ready false true 5]
             (k/eval-string s "(ns kc (:require [klara.jit.staged :as staged] [klara.compiler :as compiler] [klara.stage :refer [run]]))
               (defn calc [expr env]
                 (cond (number? expr) expr
                       (keyword? expr) (get env expr)
                       :else (let [[op a b] expr]
                               (case op :+ (+ (calc a env) (calc b env)) :* (* (calc a env) (calc b env))))))
               (def model [:+ [:* :x :x] 1])
               (defn drive [env] (calc model env))
               (def r (staged/residual (compiler/reference 'kc/drive)))
               (def o (compiler/prepare (compiler/reference 'kc/drive) {:recipe (fn [_] r) :name 'kc/drive}))
               [(:status o)
                (.contains (pr-str r) \"calc\")                  ; no call of the interpreter is left
                (contains? (set (map first (:premises o))) 'kc/model)
                ((run r) {:x 2})]"))))))
