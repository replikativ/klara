(ns klara.selection-test
  (:require [clojure.test :refer [deftest is]] [klara.stage :as stage]
            [klara.defs :as defs] [klara.world :as world] [klara.eval :as ev]
            [klara.compile.infer-affine :as affine] [klara.compile.core :as compiler]))

(defn fixture []
  (let [w (world/make-world)] (defs/define! w '(def f (fn [x] (+ x 1))))
    [(world/snapshot w) (defs/lookup (world/snapshot w) 'f)]))

(defn candidate [f variant priority predicate]
  (assoc (stage/executable f #{[:captures []] [:arg 0 predicate]} inc {:test :selection})
         :selection {:variant variant :priority priority}))

(deftest explicit-priority-ties-and-failed-guards-are-order-independent
  (let [[root f] (fixture)
        a (candidate f :a 10 :long) b (candidate f :b 10 :number)
        high (candidate f :high 20 :double)]
    (doseq [order [[a b high] [high b a] [b a high]]]
      (let [cache (stage/make-cache)]
        (doseq [exe order] (stage/install! cache exe))
        (is (= 3 (count (stage/executables cache))))
        (is (= :a (get-in (stage/enter cache f [] [1] root []) [:selection :variant])))
        (is (= :high (get-in (stage/enter cache f [] [1.5] root []) [:selection :variant])))
        (is (nil? (stage/enter cache f [] [:bad] root [])))))))

(deftest named-slot-replacement-and-legacy-order-are-explicit
  (let [[root f] (fixture) cache (stage/make-cache)
        a (candidate f :a 0 :long) b (candidate f :b 0 :long)]
    (stage/install! cache b) (stage/install! cache a)
    (is (= :a (get-in (stage/enter cache f [] [1] root []) [:selection :variant])))
    (stage/install! cache (assoc-in b [:selection :priority] 1))
    (is (= 2 (count (stage/executables cache))))
    (is (= :b (get-in (stage/enter cache f [] [1] root []) [:selection :variant])))
    (stage/clear! cache)
    (doseq [[tag pred] [[:first :number] [:second :long]]]
      (stage/install! cache (assoc (stage/executable f #{[:arg 0 pred]} inc {:test :legacy}) :tag tag)))
    (is (= :first (:tag (stage/enter cache f [] [1] root []))))
    (is (= 2 (count (stage/executables cache))))))

(deftest malformed-selection-does-not-publish
  (let [[_ f] (fixture) cache (stage/make-cache)]
    (doseq [policy [{:variant :a} {:variant "a" :priority 1}
                    {:variant :a :priority 1.5} {:variant :a :priority 0 :unchecked true}]]
      (is (= :invalid-selection
             (try (stage/install! cache (assoc (candidate f :a 0 :long) :selection policy)) nil
                  (catch clojure.lang.ExceptionInfo e (:reason (ex-data e)))))))
    (is (empty? (stage/executables cache)))))

(deftest direct-entry-site-refreshes-after-higher-priority-publication
  (let [w (world/make-world) _ (defs/define! w '(def f (fn [x] (+ x 1))))
        root (world/snapshot w) f (defs/lookup root 'f) cache (stage/make-cache)
        exe (compiler/compile-def w 'f {:mode :baseline}) site (:direct-entry @cache)]
    (stage/install! cache (assoc exe :selection {:variant :slow :priority 0}))
    (is (= :slow (get-in (site f [1] root) [:selection :variant])))
    (stage/install! cache (assoc exe :selection {:variant :fast :priority 10}))
    (is (= :fast (get-in (site f [1] root) [:selection :variant])))
    (stage/clear! cache)
    (is (nil? (site f [1] root)))))

(deftest pinned-world-validity-precedes-selection-and-sweep-refreshes-order
  (let [w (world/make-world) _ (defs/define! w '(def f (fn [x] (+ x 1))))
        _ (defs/define! w '(def g 1)) root (world/snapshot w) f (defs/lookup root 'f)
        cache (stage/make-cache)
        low (candidate f :low 0 :long)
        guards (conj (:guards low) [:world 'g (:value-id (world/entry* root 'g))])
        high (assoc (stage/executable f guards inc {:test :world-selection})
                    :selection {:variant :high :priority 10})]
    (stage/install! cache low) (stage/install! cache high)
    (defs/define! w '(def g 2))
    (is (= :low (get-in (stage/enter cache f [] [1] (world/snapshot w) []) [:selection :variant])))
    (is (= :high (get-in (stage/enter cache f [] [1] root []) [:selection :variant])))
    (is (= 1 (stage/invalidate! cache (world/snapshot w))))
    (is (= :low (get-in (stage/enter cache f [] [1] root []) [:selection :variant])))))

(deftest immutable-evidence-site-uses-the-same-priority-order
  (let [root world/empty-root
        code (defs/eval-form root '(code (fn [xs]
                                          (loop [i 0 acc [0]]
                                            (if (< i (count xs))
                                              (recur (inc i) (assoc acc 0 (+ (nth acc 0) (nth xs i)))) acc)))))
        p (affine/prepare root code {:parameter-layouts [:long-vector]})
        exe (.-executable ^klara.compile.staged.Prepared p)
        f (defs/eval-form root (list 'run (list 'quote code)))
        cache (stage/make-cache) site (stage/make-evidence-site cache f)
        evidence (stage/refine-argument :long-vector [1 2 3])]
    (stage/install! cache (assoc exe :selection {:variant :low :priority 0}))
    (is (= :low (get-in (site evidence root []) [:selection :variant])))
    (stage/install! cache (assoc exe :selection {:variant :high :priority 10}))
    (is (= :high (get-in (site evidence root []) [:selection :variant])))
    (is (= [6] ((:invoke1 (site evidence root [])) [1 2 3])))))
