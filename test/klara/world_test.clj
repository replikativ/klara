(ns klara.world-test
  "Roots, one-CAS publication, forks, fibers; CodeId α-canonicity."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.core :as c]
            [klara.world :as w]
            [klara.expand :as x]
            [klara.defs :as d]))

(deftest publication-is-one-cas
  (let [wo (w/make-world)
        n-threads 8 n-each 50
        seen-roots (atom [])
        ws (mapv (fn [t] (future (dotimes [i n-each]
                                   (w/publish! wo #(w/put-entry % (symbol (str "v" t "-" i))
                                                                {:kind :def :value i :reads #{}
                                                                 :code-id (str i) :value-id (str i)}))
                                   (swap! seen-roots conj (w/snapshot wo)))))
                 (range n-threads))]
    (run! deref ws)
    (let [root (w/snapshot wo)]
      (is (= (* n-threads n-each) (:version root) (count (:defs root))) "no lost update")
      (is (every? #(= (:version %) (count (:defs %))) @seen-roots)
          "every observed root is internally consistent: version and definitions move together"))))

(deftest commit-rebases-or-retries
  (let [wo (w/make-world)
        base (w/snapshot wo)
        put (fn [sym] #(w/put-entry % sym {:kind :def :value 1 :reads #{} :code-id "h" :value-id "h"}))]
    (w/publish! wo (put 'other))
    (is (not= ::w/retry (w/commit! wo base #{[:absent 'mine]} (put 'mine)))
        "reads still hold in the new root: rebase without recomputation")
    (is (= #{'other 'mine} (set (keys (:defs (w/snapshot wo))))))
    (is (= ::w/retry (w/commit! wo base #{[:absent 'other]} (put 'x)))
        "a read that broke forces recomputation")))

(deftest forks-and-fibers
  (let [wo (w/make-world)]
    (d/define! wo '(def a 1))
    (let [fk (w/fork wo) fib (w/fiber wo)]
      (d/define! wo '(def a 2))
      (d/define! fk '(def a 3))
      (is (= [2 3 1 1] [(d/lookup (w/snapshot wo) 'a) (d/lookup (w/snapshot fk) 'a)
                        (d/eval-in fib 'a) (d/lookup (:parent fk) 'a)]))
      (w/raise-basis! fib)
      (is (= 2 (d/eval-in fib 'a)))
      (is (= [1 2] (map #(get-in % [:defs 'a :version]) [(:parent fk) (w/snapshot wo)])))
      (is (= 2 (count (get-in (w/snapshot wo) [:defs 'a :history])))))))

(deftest code-ids
  (let [cid #(:code-id (x/expand-recorded % w/empty-root))]
    (is (= (cid '(fn [a b] (+ a b))) (cid '(fn [x y] (+ x y)))) "α-equivalent")
    (is (not= (cid '(fn [a b] (+ a b))) (cid '(fn [a b] (+ b a)))))
    (is (= (cid '{:a 1 :b 2}) (cid '{:b 2 :a 1})) "quoted maps are order-free")
    (is (= (c/code-id (c/lam 1 (c/local 0))) (c/code-id (c/lam 1 (c/local 0)))))))
