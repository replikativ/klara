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

(deftest profile-facts-become-speculations   ; L4.jit.staged
  (let [s (session)]
    (k/eval-string s "(ns pf (:require [klara.jit :as jit] [klara.jit.staged :as staged] [klara.compiler :as compiler]
                                       [klara.effect :refer [perform handle]]))
      (defn staged-spec [ctx default] (staged/specialize ctx))")
    (testing "a branch never taken: the hot path compiles, the effect stays in the fallback"
      (is (= [:ready 1 true]
             (k/eval-string s "(defn settle [xs] (loop [i 0 b 0] (if (< i (count xs))
                                 (let [a (nth xs i)] (if (neg? a) (recur (inc i) (+ b (perform :review a))) (recur (inc i) (+ b a))))
                                 b)))
               (dotimes [_ 3] (settle (vec (range 200))))
               (def o (jit/compile! 'pf/settle {:specializer staged-spec}))
               [(:status o) (:speculations o)
                (= 4900 (handle {:review (fn [k a] (k 0))} (settle (assoc (vec (range 100)) 50 -5))))]"))))
    (testing "an argument always the same: the interpreter is specialized to it automatically (no user generator)"
      (is (= [:ready true 7 42]
             (k/eval-string s "(defn calc [expr env]
                 (cond (number? expr) expr
                       (keyword? expr) (get env expr)
                       :else (let [[op a b] expr]
                               (case op :+ (+ (calc a env) (calc b env)) :* (* (calc a env) (calc b env))))))
               (def model [:+ [:* :x :x] 3])
               (dotimes [i 200] (calc model {:x i}))
               (def o (jit/compile! 'pf/calc {:specializer staged-spec}))
               (def cand (pr-str (:candidate (compiler/explain calc))))
               [(:status o)
                ;; under the guard the interpreter is gone: only the model's arithmetic is left
                (boolean (re-find #\"\\(klara.jit/same\\? \\S+ \\[:\\+ \\[:\\* :x :x\\] 3\\]\\) \\(\\+ \\(\\* \\(get \\S+ :x\\) \\(get \\S+ :x\\)\\) 3\\)\" cand))
                (calc model {:x 2})
                (calc [:+ :x 1] {:x 41})]"))))
    (testing "a hot call of a definition that loops stays a call (no guard on a definition)"
      (is (= [:ready 10]
             (k/eval-string s "(defrecord E [val next])
               (defn mk [n] (when (pos? n) (->E n (mk (dec n)))))
               (defn shorter? [x y] (loop [x x y y] (cond (nil? y) false (nil? x) true :else (recur (:next x) (:next y)))))
               (defn tl [x y z] (if (shorter? y x) (tl (tl (:next x) y z) (tl (:next y) z x) (tl (:next z) x y)) z))
               (defn len [x] (loop [x x n 0] (if x (recur (:next x) (inc n)) n)))
               (dotimes [_ 20] (tl (mk 15) (mk 10) (mk 6)))
               [(:status (jit/compile! 'pf/tl {:specializer staged-spec})) (len (tl (mk 15) (mk 10) (mk 6)))]"))))
    (testing "a call site that always called the same function: inlined under a guard"
      (is (= [:ready 1 9]
             (k/eval-string s "(defn twice [f x] (f (f x)))
               (def add3 (fn [y] (+ y 3)))
               (dotimes [i 200] (twice add3 i))
               (def o (jit/compile! 'pf/twice {:specializer staged-spec}))
               [(:status o) (min 1 (:speculations o)) (twice add3 3)]"))))))

(deftest other-constructs-are-kept   ; L4.jit.staged L2.view.free L4.check.code
  (testing "throw, try, interop, letrec and several arities: interpreted, and kept whole in residuals"
    (let [s (session)]
      (is (= [[:caught 3 "AB" 3 [1 2]] [:checked :checked :checked :checked :ready]]
             (k/eval-string s "(ns oc (:require [klara.jit.staged :as staged] [klara.compiler :as compiler]))
               (defn t1 [x] (try (if (pos? x) (throw (ex-info \"no\" {})) x) (catch Exception e :caught)))
               (defn t2 [x] (try x (finally (str x))))
               (defn t3 [s] (.toUpperCase s))
               (defn t4 [n] (letfn [(ev [k] (if (zero? k) true (od (dec k)))) (od [k] (if (zero? k) false (ev (dec k))))] (if (ev n) (* 2 n) n)))
               (defn t5 [x] (let [f (fn ([a] [a]) ([a b] [a b]))] (f x 2)))
               (defn run [q & args] (apply staged/interpret (compiler/reference q) args))
               [[(run 'oc/t1 1) (run 'oc/t2 3) (run 'oc/t3 \"ab\") (run 'oc/t4 3) (run 'oc/t5 1)]
                ;; admitted by the checker; the backend does not compile try, interop and letrec yet
                (mapv (fn [q] (let [o (compiler/prepare (compiler/reference q) {:recipe (fn [r] (staged/residual r)) :name q})]
                                (if (= :L4.lower.subset (:rule o)) :checked (:status o))))
                      ['oc/t1 'oc/t2 'oc/t3 'oc/t4 'oc/t5])]"))))))

(deftest hints-survive-generation   ; L2.view.total L4.lower.hint L4.jit.staged
  (testing "a let's host hint is in its view and in the residual, so the backend still checks it and avoids reflection"
    (let [s (session)]
      (is (= ['booleans true]
             (k/eval-string s "(ns ht (:require [klara.jit.staged :as staged] [klara.compiler :as compiler] [klara.code :as code]))
               (defn first-flag [n] (let [^booleans a (boolean-array n true)] (aget a 0)))
               (def r (compiler/reference 'ht/first-flag))
               [(:tag (code/view (:body (code/view r))))
                (.contains (pr-str (:compiled (compiler/explain (do (compiler/optimize! 'ht/first-flag {:recipe staged/residual}) first-flag))))
                           \"isInstance\")]"))))))

