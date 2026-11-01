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
  (testing "the investor does not run an impure definition to measure it: it compiles it unmeasured"
    (is (= [1500 1500 :compiled :baseline]
           (run (str header "(require '[klara.investor :as investor])
                 (def buf (long-array 1))
                 (defn bump! [a] (loop [i 0] (if (< i 50) (do (aset a 0 (inc (aget a 0))) (recur (inc i))) (aget a 0))))
                 (dotimes [_ 30] (bump! buf))
                 (def before (aget buf 0))
                 (def d (investor/consider 'adv/bump! {:baseline-ns 0 :explore-ns 0}))
                 [before (aget buf 0) (:decision d) (:tier d)]"))))))

(deftest specializers-may-decline   ; L4.prepare.declined
  (testing "the in-place specializer declines a function without an accumulator to own"
    (is (= :declined
           (run (str header "(defn f [x] (* x 2)) (dotimes [_ 3] (f 1))
                 (:status (jit/prepare 'adv/f {:specializer own/in-place :certificate {:kind :in-place}}))"))))))

(deftest parallel-jobs-share-profiles-safely   ; L3.job.parallel
  (testing "preparations running at the same time read and write the same profiles without failing"
    (is (= #{:ready}
           (run (str header "(defn wc [ws] (loop [i 0 m {}] (if (< i (count ws)) (recur (inc i) (assoc m (nth ws i) i)) m)))
                 (def ws (vec (range 50)))
                 (dotimes [_ 200] (wc ws))
                 (set (for [_ (range 6)
                            o (job/run-all {:budget {:steps 50000000}}
                                (for [_ (range 6)] (fn [] (wc ws) (:status (jit/prepare 'adv/wc)))))]
                        (:value o)))"))))))

(deftest the-investor-tiers-by-time-spent   ; L4.jit.tiers
  (testing "below the baseline cost nothing happens; then compiled as it is, unmeasured; exploring only past its cost"
    (is (= [:not-hot :baseline true]
           (run (str header "(require '[klara.investor :as investor])
                 (defn sq [x] (* x x))
                 (dotimes [_ 200] (sq 3))
                 (def s (investor/spent-ns (jit/context 'adv/sq)))
                 [(:decision (investor/consider 'adv/sq {:baseline-ns (inc s)}))
                  (:tier (investor/consider 'adv/sq {:baseline-ns 0 :explore-ns (inc s)}))
                  ;; explored: alternatives were prepared and measured
                  (some? (:alternatives (investor/consider 'adv/sq {:baseline-ns 0 :explore-ns 0})))]"))))))

(deftest host-functions-in-definitions-are-not-assumed-pure   ; L4.facts.pure L0.surface.defrecord
  (testing "a definition holding an impure host function makes its callers impure; record constructors are pure"
    (is (= [false true]
           (run (str header "(def say! println)
                 (defn greet [x] (say! x))
                 (defrecord P [x y])
                 (defn mk [x] (->P x x))
                 [(:pure (jit/pure? 'adv/greet)) (:pure (jit/pure? 'adv/mk))]"))))))

(deftest the-investor-runs-between-forms   ; L4.jit.trigger
  (testing "with the automatic investor, a definition that became hot is compiled after the form that ran it"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (k/automatic-investor! s {:baseline-ns 0 :explore-ns Long/MAX_VALUE})
      (is (= [:interpreted :compiled]
             [(k/eval-string s "(ns trig (:require [klara.compiler :as compiler])) (defn sq [x] (* x x)) (:kind (compiler/explain sq))")
              (do (k/eval-string s "(ns trig) (dotimes [i 100] (sq i))")
                  (if (= :interpreted (k/eval-string s "(ns trig) (:kind (compiler/explain sq))")) :interpreted :compiled))])))))

(deftest baseline-code-is-promoted   ; L4.jit.trigger L4.jit.tiers
  (testing "a definition compiled at the baseline counts its entries and is explored once its extrapolated time passes the exploring cost"
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (k/eval-string s "(ns promo (:require [klara.compiler :as compiler] [klara.investor :as investor] [klara.jit :as jit])) (defn sq [x] (* x x)) (dotimes [i 100] (sq i))")
      (let [first-d (k/eval-string s "(ns promo) (:tier (investor/consider 'promo/sq {:baseline-ns 0 :explore-ns Long/MAX_VALUE}))")
            spent (k/eval-string s "(ns promo) (:spent-ns (peek (get investor/decisions 'promo/sq)))")
            _ (k/eval-string s "(ns promo) (dotimes [i 1000] (sq i))")
            counted (k/eval-string s "(ns promo) (:entries (compiler/explain sq))")
            promoted (k/eval-string s (str "(ns promo) (mapv (juxt :name :tier) (investor/tick! '[promo] {:baseline-ns 0 :explore-ns " (* 5 spent) "}))"))]
        (is (= :baseline first-d))
        (is (<= 1000 counted))
        (is (= [['promo/sq :explored]] (mapv (fn [[q t]] [q (if (= t :baseline) :baseline :explored)]) promoted)))))))


(deftest the-investor-decides-callees-first   ; L4.jit.tiers
  (testing "definitions are decided after the ones they call, so a caller is measured with its callees compiled"
    (is (= '[adv/leaf adv/mid adv/top adv/loner]
           (run (str header "(require '[klara.investor :as investor])
                 (defn leaf [x] (* x x))
                 (defn mid [x] (leaf (inc x)))
                 (defn top [x] (mid x))
                 (defn loner [x] x)
                 (investor/callees-first '[adv/top adv/mid adv/leaf adv/loner])"))))))
