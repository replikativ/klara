(ns klara.compile.literal-test
  (:require [clojure.test :refer [deftest is]] [klara.core :as core]
            [klara.expand :as expand] [klara.eval :as ev] [klara.world :as world]
            [klara.defs :as defs] [klara.compile.core :as compiler]
            [klara.compile.core-test :refer [setup observe]] [klara.stage :as stage]
            [klara.repl :as repl] [klara.compile.staged]))

(defn outcome [f args]
  (try (let [v (apply f args)] [:value (class v) v])
       (catch Throwable t [:error (class t)])))

(deftest literal-size-and-explicit-constructor-are-distinct
  (doseq [n [0 1 2 8 9 16]]
    (let [literal (into {} (map (fn [i] [(keyword (str "k" i)) (list '+ 'x i)]) (range n)))
          form (list 'fn '[x] literal) w (setup form)
          f (defs/lookup (world/snapshot w) 'f)
          expected ((eval form) 3)]
      (is (= (class expected) (class (f 3))))
      (doseq [mode [:baseline :optimizing]]
        (let [cache (stage/make-cache) exe (compiler/compile-def w 'f {:mode mode})]
          (stage/install! cache exe)
          (is (= expected (stage/with-cache cache (f 3))))
          (is (= (class expected) (class (stage/with-cache cache (f 3)))))
          (is (pos? (:hits (stage/stats cache))))
          (is (zero? (:fallbacks (stage/stats cache))))))))
  (is (= clojure.lang.PersistentHashMap
         (class (ev/run (expand/expand-expr '(hash-map :a 1 :b 2) world/empty-root)))))
  ;; Previously stored Core keeps its meaning; only new literal expansion changes.
  (is (= clojure.lang.PersistentHashMap
         (class (ev/run (core/prim 'hash-map (core/quote* :a) (core/quote* 1)))))))

(deftest unknown-keys-check-after-ordered-values
  (let [form '(fn [x y z] {x (/ 1 z) y 2}) w (setup form)
        f (defs/lookup (world/snapshot w) 'f) reference (eval form)]
    (doseq [mode [:baseline :optimizing]]
      (let [cache (stage/make-cache)]
        (stage/install! cache (compiler/compile-def w 'f {:mode mode}))
        (doseq [args [[1 2 1] [1 1 1] [1 1 0] [1 2 0]]]
          (is (= (outcome reference args) (outcome f args)))
          (is (= (outcome reference args) (stage/with-cache cache (outcome f args))))))))
  (is (thrown? IllegalArgumentException
               (expand/expand-expr '(fn [] {(quote :a) 1 :a 2}) world/empty-root))))

(deftest optimizers-retain-failing-unused-literals
  (let [w (setup '(fn [x] (let [unused (literal-map :a x :a 2)] 3)))]
    (doseq [mode [:baseline :optimizing]]
      (let [cache (stage/make-cache)]
        (stage/install! cache (compiler/compile-def w 'f {:mode mode}))
        (is (= (observe w '(f 4) (stage/make-cache)) (observe w '(f 4) cache)))
        (is (= :error (first (observe w '(f 4) cache))))))))

(deftest host-and-guest-bindings-do-not-capture-literal-lowering
  (let [w (setup '(fn [literal-map hash-map object-array aset]
                    {:a literal-map :b hash-map :c object-array :d aset}))
        empty-host-ns (create-ns (gensym "backend-test"))]
    (try
      (let [exe (binding [*ns* empty-host-ns] (compiler/compile-def w 'f {:mode :baseline}))
            cache (stage/make-cache)]
        (stage/install! cache exe)
        (is (= [:value {:a 1 :b 2 :c 3 :d 4} ""] (observe w '(f 1 2 3 4) cache))))
      (finally (remove-ns (ns-name empty-host-ns)))))
  (let [s (repl/session)]
    (is (empty? (:errors (repl/eval-response s "(ns custom) (defn literal-map [x] :shadow) (defn f [x] {:a x})"))))
    (is (= ":shadow" (repl/eval-string s "(literal-map 1)")))
    (is (= "{:a 1}" (repl/eval-string s "(f 1)")))))

(deftest zero-arity-construction-retains-empty-singleton
  (let [w (setup '(fn [] (literal-map))) cache (stage/make-cache)]
    (stage/install! cache (compiler/compile-def w 'f {:mode :baseline}))
    (let [f (defs/lookup (world/snapshot w) 'f)]
      (is (identical? clojure.lang.PersistentArrayMap/EMPTY (f)))
      (is (identical? clojure.lang.PersistentArrayMap/EMPTY (stage/with-cache cache (f)))))))

(deftest primitive-valued-literals-use-direct-array-stores
  (let [w (setup '(fn [n] (loop [i 0 rows []]
                            (if (< i n)
                              (recur (inc i) (conj rows {:square (* i i) :index i})) rows))))
        warnings (java.io.StringWriter.)
        exe (binding [*warn-on-reflection* true *err* warnings]
              (compiler/compile-def w 'f {:mode :baseline}))
        cache (stage/make-cache)]
    (is (= "" (str warnings)))
    (stage/install! cache exe)
    (is (= [:value [{:square 0 :index 0} {:square 1 :index 1} {:square 4 :index 2}] ""]
           (observe w '(f 3) cache)))
    (is (pos? (:hits (stage/stats cache))))))
