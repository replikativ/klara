(ns klara.adversarial-test
  "Wrong candidates. The natural specializers never produce these, so the
  other tests cannot catch a checker, certifier or lowering that admits
  them. Each case states what the kernel must do with a candidate that
  differs from its reference in a way that is easy to miss: reject it, or
  run it so that it cannot be told apart from the reference."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.host.api :as k]))

(defn- session [] (k/session {:roots ["lib"] :out (java.io.StringWriter.)}))

(defn- run
  "Evaluate src in a fresh session. These candidates are wrong by design, so
   a case that does not stop is a failure (:timeout), never a hung suite."
  [src]
  (let [f (future (try (k/eval-string (session) src) (catch Throwable e [:threw (str e)])))
        r (deref f 60000 ::timeout)]
    (when (= ::timeout r) (future-cancel f))
    r))

(def ^:private header
  "(ns adv (:require [klara.stage :refer [code esc lift run]] [klara.compiler :as compiler]
                     [klara.code :as c] [klara.jit :as jit] [klara.own :as own] [klara.job :as job]
                     [klara.effect :refer [perform handle]]))")

(defn- status [ref-src cand-src & [opts]]
  (run (str header "(:status (compiler/prepare (code " ref-src ") {:recipe (fn [_] (code " cand-src "))"
            (or opts "") "}))")))

(deftest constants-are-compared-by-representation   ; L4.check.const L4.check.prim
  (testing "numbers of another class"
    (is (= :rejected (status "(fn [x] (+ x 1))" "(fn [x] (+ x 1N))")))
    (is (= :rejected (status "(fn [x] (+ x 1))" "(fn [x] (+ x 1.0))"))))
  (testing "collections of another class"
    (is (= :rejected (status "(fn [x] (conj [1 2] x))" "(fn [x] (conj '(1 2) x))")))
    (is (= :rejected (status "(fn [] #{1 2 3})" "(fn [] (esc (lift (sorted-set 3 2 1))))")))
    (is (= :rejected (status "(fn [] {:a 1 :b 2 :c 3})" "(fn [] (esc (lift (hash-map :a 1 :b 2 :c 3))))"))))
  (testing "metadata"
    (is (= :rejected (status "(fn [] [1])" "(fn [] (esc (lift (with-meta [1] {:tag 1}))))"))))
  (testing "controls: the same constant is admitted"
    (is (= :ready (status "(fn [x] (conj [1 2] x))" "(fn [x] (conj [1 2] x))")))
    (is (= :ready (status "(fn [x] (+ x 1N))" "(fn [x] (+ x 1N))")))))

(deftest the-definition-being-replaced-is-opaque   ; L4.check.self
  (testing "a candidate that is the reference only through itself is rejected"
    (is (= :rejected
           (run (str header "(defn h [x] (+ x 1))
                 (:status (compiler/prepare (compiler/reference 'adv/h)
                                            {:recipe (fn [_] (code (fn [x] (adv/h x)))) :name 'adv/h}))")))))
  (testing "control: recursive calls that match the reference's are admitted"
    (is (= :ready
           (run (str header "(defn fib [n] (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
                 (:status (compiler/optimize! 'adv/fib))"))))))

(deftest guards-cannot-run-klara-code   ; L4.check.speculate
  (testing "= forces lazy sequences, so it is not a total guard"
    (is (= :rejected
           (run (str header "(defn pick [x y] 0)
                 (:status (compiler/prepare (compiler/reference 'adv/pick)
                   {:recipe (fn [_] (code (fn [x y] (esc (jit/guard (code (= x y)) (code 0) (code 0))))))
                    :name 'adv/pick}))"))))))

(deftest same?-cannot-be-fooled   ; L4.check.speculate-value
  (testing "collections must be the very object; scalars equal in value, class and metadata"
    (is (= [false false false false false true true false false]
           (run (str header "(def v [1 {:a :b}])
                             [(jit/same? (with-meta {:x 1} {:r 1}) {:x 1})
                              (jit/same? {1 :a} {1N :a})
                              (jit/same? #{1} #{1N})
                              (jit/same? (map inc [1]) (lift '(2)))
                              (jit/same? [1 {:a :b}] [1 {:a :b}])
                              (jit/same? v v)
                              (jit/same? :k :k)
                              (jit/same? 1 1N)
                              (jit/same? 'x (with-meta 'x {:m 1}))]"))))))

(deftest owned-transients-are-placed-not-matched   ; L4.check.in-place
  (testing "a second, equal transient outside the loop is not an owned loop init"
    (is (= :rejected
           (run (str header "(defn build [n]
                   (let [a (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc i)) acc)) b []] [a b]))
                 (def tr (c/make {:op :app :fn (c/make {:op :host :name 'klara.core/own}) :args [(lift [])]}))
                 (def cand (code (fn [n]
                   (let [a ((fn lp [i acc] (if (< i n) (recur (inc i) (klara.core/conj! acc i))
                                                (klara.core/persistent! acc)))
                            0 (esc tr))
                         b (esc tr)]
                     [a b]))))
                 (:status (compiler/prepare (compiler/reference 'adv/build)
                                            {:recipe (fn [_] cand) :certificate {:kind :in-place} :name 'adv/build}))"))))))

(deftest owned-loops-survive-multi-shot-resumption   ; L4.check.in-place
  (testing "compiled code leaves before the loop; continuations inside it are resumed twice"
    (is (= [:ready true]
           (run (str header "(defn pick [] (perform :pick))
                 (defn collect2 [n] (let [base (pick)]
                   (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc (+ i base (pick)))) acc))))
                 (def both (fn [k] [(k 0) (k 100)]))
                 (def before (handle {:pick both} (collect2 2)))
                 (def o (jit/compile! 'adv/collect2 {:specializer own/in-place :certificate {:kind :in-place}}))
                 [(:status o) (= before (handle {:pick both} (collect2 2)))]"))))))

(deftest the-erasure-check-is-budgeted   ; L4.check.in-place L4.prepare.job
  (testing "a candidate whose erasure check does not terminate exhausts the budget"
    (is (= :exhausted
           (run (str header "(defn f [x] (f (inc x))) (defn g [x] (g (inc x)))
                 (:status (compiler/prepare (code (fn [x] (f x)))
                   {:recipe (fn [_] (code (fn [x] (g x)))) :budget {:steps 100000}
                    :certificate {:kind :in-place}}))"))))))

(deftest views-make-only-what-the-expander-allows   ; L2.view.make
  (testing "code/make refuses host functions Klara does not support"
    (is (= :L2.view.make
           (run (str header "(try (c/make {:op :host :name 'clojure.core/eval})
                              (catch Exception e (:rule (ex-data e))))"))))))

(deftest specializers-run-inside-the-preparation-job   ; L4.prepare.job
  (testing "a specializer's work is budgeted: an endless one exhausts the preparation"
    (is (= :exhausted
           (run (str header "(defn f [x] x)
                 (dotimes [_ 3] (f 1))
                 (defn forever [ctx default] (loop [] (recur)))
                 (:status (jit/prepare 'adv/f {:specializer forever :budget {:steps 10000}}))"))))))

(deftest malformed-candidates-are-rejected   ; L4.lower.subset
  (testing "a recur without its loop is rejected, not compiled"
    (is (= :rejected
           (run (str header "(defn idf [x] x)
                 (def bogus (c/make {:op :fn :params '[x]
                                     :body (c/make {:op :recur :target 'nowhere :arity 7 :args [(lift 1) (lift 2)]})}))
                 (:status (compiler/prepare (compiler/reference 'adv/idf) {:recipe (fn [_] bogus)}))"))))))

(deftest measuring-runs-only-pure-code   ; L4.facts.pure
  (testing "purity: pure code, code that writes its own arrays, and impure code"
    (is (= [true true false false]
           (run (str header "(defn sq [x] (* x x))
                 (defn fill [n] (let [a (long-array n)] (aset a 0 1) (aget a 0)))
                 (def buf (java.util.ArrayList.))
                 (defn log! [x] (.add buf x))
                 (def counter (atom 0))
                 (defn bump [] (swap! counter inc))
                 (mapv #(:pure (jit/pure? %)) ['adv/sq 'adv/fill 'adv/log! 'adv/bump])")))))
  (testing "the investor does not run an impure definition to measure it"
    (is (= [1500 1500 :unmeasurable]
           (run (str header "(require '[klara.investor :as investor])
                 (def buf (java.util.ArrayList.))
                 (defn log! [b x] (loop [i 0] (if (< i 50) (do (.add b x) (recur (inc i))) (.size b))))
                 (dotimes [_ 30] (log! buf 1))
                 (def before (.size buf))
                 (def d (investor/consider 'adv/log!))
                 [before (.size buf) (:decision d)]"))))))

(deftest specializers-may-decline   ; L4.prepare.declined
  (testing "the in-place specializer declines a function without an accumulator to own"
    (is (= :declined
           (run (str header "(defn f [x] (* x 2)) (dotimes [_ 3] (f 1))
                 (:status (jit/prepare 'adv/f {:specializer own/in-place :certificate {:kind :in-place}}))"))))))
