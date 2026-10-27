(ns klara.x1-test
  "X1's pass criteria (doc/research/C-staging.md §6 E1), ported from
  lambda-join v0/test/v0/macros_test.clj to the S1 API: macros are world
  entries, expansion records its reads (now including negative lookups),
  re-expansion cuts off on the α-canonical expansion hash (the CodeId of
  the core term)."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.core :as c]
            [klara.world :as w]
            [klara.expand :as x]
            [klara.eval :as ev]
            [klara.defs :as d]))

(defn- e0-world
  "E0's setup: twice as +, f uses it."
  []
  (let [wo (w/make-world)]
    (d/define! wo '(defmacro twice [e] (qq (+ ~e ~e))))
    (d/define! wo '(def f (fn* [y] (twice y))))
    wo))

(defn- call [wo sym & args] (apply (d/lookup (w/snapshot wo) sym) args))
(defn- f3 [wo] (call wo 'f 3))
(defn- entry [wo sym] (w/entry* (w/snapshot wo) sym))

(deftest macros-are-world-entries
  (let [wo (e0-world)
        tw (entry wo 'twice)]
    (is (= :macro (:kind tw)))
    (is (ev/closure? (:value tw)) "the transformer is a T0 closure, not host code")
    (is (contains? (:reads (entry wo 'f)) [:macro 'twice (:value-id tw)])
        "the expansion read is a dependency (E0 had none)")
    (is (= '#{f} (w/dependents (w/snapshot wo) 'twice)))
    (is (c/wf? (:code (entry wo 'f))) "definitions are stored as core terms")))

(deftest i-redefine-then-invalidate
  (let [wo (e0-world)]
    (is (= 6 (f3 wo)))
    (d/define! wo '(defmacro twice [e] (qq (* ~e ~e))))
    (testing "between publication and invalidation f is pending, not stale"
      (is (= :pending (:klara/error (ex-data (try (f3 wo) (catch Exception e e)))))))
    (let [{:keys [stale reexpanded]} (d/invalidate! wo 'twice)]
      (is (= '[f] stale) "E0 reported nothing stale")
      (is (= '[f] reexpanded)))
    (is (= 9 (f3 wo)))))

(deftest ii-output-preserving-refactor-cuts-off
  (let [wo (e0-world)
        before (entry wo 'f)
        n0 @x/expansions]
    (d/define! wo '(defmacro twice [x] (list (quote +) x x)))
    (is (not= (:code-id (entry wo 'twice)) (:code-id before))
        "the transformer itself did change")
    (let [{:keys [stale cutoff reexpanded]} (d/invalidate! wo 'twice)]
      (is (= '[f] cutoff))
      (is (= '[f] reexpanded) "re-expanded, compared, cut off")
      (is (empty? stale)))
    (is (= 2 (- @x/expansions n0)) "one expansion for the macro, one for f")
    (let [after (entry wo 'f)]
      (is (identical? (:value before) (:value after)) "no re-evaluation")
      (is (= (:code-id before) (:code-id after)))
      (is (= (:history before) (:history after)))
      (is (not= (:reads before) (:reads after)) "reads now name the new transformer"))
    (is (= 6 (f3 wo)))))

(deftest iii-fork-isolation
  (let [wo (e0-world)
        fk (w/fork wo)]
    (d/define! fk '(defmacro twice [e] (qq (* ~e ~e))))
    (is (= '[f] (:stale (d/invalidate! fk 'twice))))
    (is (= 9 (f3 fk)))
    (is (= 6 (f3 wo)) "parent's f untouched")
    (is (identical? (:parent fk) (w/snapshot wo)) "the fork pinned the parent root")
    (is (not= (:code-id (entry fk 'twice)) (:code-id (entry wo 'twice))))
    (testing "the parent's own invalidation sees nothing to do"
      (is (= '[f] (:green (d/invalidate! wo 'twice))))
      (is (= 6 (f3 wo))))))

(deftest iv-basis-isolation
  (let [wo (e0-world)
        fib (w/fiber wo)]
    (d/define! wo '(defmacro twice [e] (qq (* ~e ~e))))
    (d/invalidate! wo 'twice)
    (is (= 9 (f3 wo)) "the world moved on")
    (is (= 6 (d/eval-in fib '(f 3))) "the pinned fiber still sees the old f")
    (w/raise-basis! fib)
    (is (= 9 (d/eval-in fib '(f 3))) "visible after raise-basis!")))

(deftest v-cache-keys
  (let [wo (w/make-world)]
    (d/define! wo '(defmacro inc1 [e] (qq (+ ~e 1))))
    (let [root (w/snapshot wo)
          run (fn [key-fn prog]
                (let [[term table] (x/with-memo* key-fn #(x/expand-expr prog root))]
                  [(ev/run term {:basis root}) (count table)]))
          shadow '(let* [x 1] [(inc1 x) (let* [y 2] (inc1 x))])]
      (testing "the hazard: scopes live in metadata, = and hash ignore them"
        (is (= (x/add-scope 'x 1) (x/add-scope 'x 2)))
        (is (= (hash (x/add-scope 'x 1)) (hash (x/add-scope 'x 2)))))
      (testing "uncached reference"
        (is (= [[2 2] 0] (run (constantly nil) shadow))))
      (testing "bare-form key: (inc1 x) at index 0 and at index 1 collide"
        (is (= [[2 3] 1] (run x/form-key shadow))))
      (testing "alpha (binding-qualified) key: no collision"
        (is (= [[2 2] 2] (run x/alpha-key shadow))))
      (testing "...and it still shares closed forms"
        (is (= [[6 6] 1] (run x/alpha-key '[(inc1 5) (inc1 5)]))))
      (testing "de Bruijn output: same binder depth shares even under shadowing"
        (is (= [[2 3] 1] (run x/alpha-key '(let* [x 1] [(inc1 x) (let* [x 2] (inc1 x))])))))))
  (testing "fresh expansions differ in scopes and renames, agree in CodeId"
    (let [ctx2 (x/new-ctx)
          _ (dotimes [_ 7] (x/fresh-scope! ctx2))
          e1 (x/expand-recorded '(let* [z 1] (fn* [q] [z q])) w/empty-root)
          e2 (x/expand-recorded '(let* [w 1] (fn* [z] [w z])) w/empty-root ctx2)]
      (is (= (:term e1) (:term e2)))
      (is (= (:code-id e1) (:code-id e2))))))

;; ---------------------------------------------------------------------------
;; beyond the criteria: transitive macro reads, expansion-time value reads,
;; negative lookups (the X1 gap)
;; ---------------------------------------------------------------------------

(deftest macro-through-macro
  (let [wo (e0-world)]
    (d/define! wo '(defmacro quad [e] (qq (twice (twice ~e)))))
    (d/define! wo '(def g (fn* [y] (quad y))))
    (is (= '#{quad twice}
           (into #{} (keep (fn [[k s]] (when (= :macro k) s))) (:reads (entry wo 'g)))))
    (is (= 12 (call wo 'g 3)))
    (d/define! wo '(defmacro twice [e] (qq (* ~e ~e))))
    (is (= '[f g] (:stale (d/invalidate! wo 'twice))))
    (is (= 81 (call wo 'g 3)))))

(deftest transformer-reads-a-value
  ;; the transformer calls a world function at expansion time: the user of
  ;; the macro records that value read. The macro itself does not: its
  ;; reference to the helper is late bound.
  (let [wo (w/make-world)]
    (d/define! wo '(def x1-helper (fn* [e] (list (quote +) e e))))
    (d/define! wo '(defmacro twice [e] (x1-helper e)))
    (d/define! wo '(def h (fn* [y] (twice y))))
    (is (contains? (:reads (entry wo 'h)) [:value 'x1-helper (:value-id (entry wo 'x1-helper))]))
    (is (contains? (:reads (entry wo 'twice)) [:def 'x1-helper]))
    (d/define! wo '(def x1-helper (fn* [e] (list (quote *) e e))))
    (let [r (d/invalidate! wo 'x1-helper)]
      (is (= '[h] (:stale r)) "h re-expanded")
      (is (= '[twice] (:green r)) "the macro's late-bound read holds"))
    (is (= 9 (call wo 'h 3)))))

(deftest negative-lookups-are-dependencies
  (let [wo (w/make-world)]
    (d/define! wo '(def g (fn [y] (inc y))))
    (is (contains? (:reads (entry wo 'g)) '[:absent inc]) "fell back past the world")
    (is (= 2 (call wo 'g 1)))
    (testing "a later world macro of that name re-expands g"
      (d/define! wo '(defmacro inc [y] (qq (+ 100 ~y))))
      (is (= :pending (:klara/error (ex-data (try (call wo 'g 1) (catch Exception e e))))))
      (is (= '[g] (:stale (d/invalidate! wo 'inc))))
      (is (= 101 (call wo 'g 1))))
    (testing "and a world function of that name re-expands it to a resolve"
      (d/define! wo '(def inc (fn [y] (+ 1000 y))))
      (is (= '[g] (:stale (d/invalidate! wo 'inc))))
      (is (= 1001 (call wo 'g 1)))
      (is (= '#{inc} (c/free-globals (:code (entry wo 'g))))))))

(deftest definition-time-value-reads
  (let [wo (w/make-world)]
    (d/define! wo '(def base 10))
    (d/define! wo '(def derived (* 2 base)))
    (is (= 20 (d/lookup (w/snapshot wo) (quote derived))))
    (d/define! wo '(def base 21))
    (is (= '[derived] (:stale (d/invalidate! wo 'base))))
    (is (= 42 (d/lookup (w/snapshot wo) (quote derived))))))
