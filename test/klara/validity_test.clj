(ns klara.validity-test
  "S7: per-root validity of executables. An executable's world guards are
  checked once per (executable, root) and the verdict is memoized;
  publication does no work for executables (gate R1); fibers pinned to
  old and new roots each keep their own verdict (gate R4)."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.world :as w]
            [klara.eval :as ev]
            [klara.defs :as d]
            [klara.stage :as s]))

(defn- world []
  (let [wo (w/make-world)]
    (d/define! wo '(def sq (fn [x] (* x x))))
    (d/define! wo '(def f (fn [x] (+ (sq x) 1))))
    wo))

(defn- exe-for-f
  "A host executable for f that agrees with it while sq squares."
  [root]
  (let [f (d/lookup root 'f)]
    (s/executable f (into #{[:captures []] [:arg 0 :long]} (s/world-guards (ev/closure-term f) root))
                  (fn [x] (+ (* x x) 1)) {:author :validity-test})))

(deftest verdict-once-per-root
  (let [wo (world) root (w/snapshot wo)
        cache (doto (s/make-cache) (s/install! (exe-for-f root)))]
    (s/with-cache cache (dotimes [i 1000] (is (= (inc (* i i)) (d/eval-form root (list 'f i))))))
    (is (= {:hits 1000 :revalidations 1} (select-keys (s/stats cache) [:hits :revalidations]))
        "1000 entries under one root: world guards checked once")
    (testing "runtime guards are still checked on every entry"
      (s/with-cache cache (is (= 7.25 (d/eval-form root '(f 2.5)))))
      (is (= 1 (:fallbacks (s/stats cache))))
      (is (= 1 (:revalidations (s/stats cache)))))
    (testing "an unrelated publication: one revalidation under the new root, verdict valid"
      (d/define! wo '(def unrelated 1))
      (let [root' (w/snapshot wo)]
        (s/with-cache cache (dotimes [i 100] (d/eval-form root' (list 'f i))))
        (is (= {:hits 1100 :revalidations 2} (select-keys (s/stats cache) [:hits :revalidations])))))
    (testing "an edit of sq: the verdict under the edited root is invalid, the old one stays valid"
      (d/define! wo '(def sq (fn [x] (+ x x))))
      (let [root2 (w/snapshot wo)]
        (s/with-cache cache
          (dotimes [i 100]
            (is (= (inc (+ i i)) (d/eval-form root2 (list 'f i))))
            (is (= (inc (* i i)) (d/eval-form root (list 'f i))))))
        (is (= 3 (:revalidations (s/stats cache))) "root2 checked once; root's verdict still memoized")))))

(deftest r1-publication-is-independent-of-executables
  (let [wo (world) root (w/snapshot wo)
        f (d/lookup root 'f)
        cache (s/make-cache)
        n 2000]
    ;; n executables for f, one per statics value, all reading sq
    (dotimes [i n]
      (s/install! cache (s/executable f (into #{[:captures []] [:statics [i]]}
                                              (s/world-guards (ev/closure-term f) root))
                                      (fn [x] (+ (* x x) 1)) {:author :validity-test})))
    (is (= n (count (s/executables cache))))
    (let [before (s/stats cache)]
      (dotimes [i 200] (d/define! wo (list 'def 'sq (list 'fn '[x] (list '* 'x 'x i)))))
      (is (= before (s/stats cache)) "200 publications of sq, which all n executables read: no cache work")
      (is (= n (count (s/executables cache))) "nothing was killed: invalidity is a verdict, found on entry"))
    (testing "the cost moves to entry, per executable entered"
      (let [root' (w/snapshot wo)
            p (d/eval-form root' '(fn [g] ((specialize g 3))))]
        (s/with-cache cache (p (d/lookup root' 'f)))
        (is (= n (:revalidations (s/stats cache)))
            "each candidate of the entered CodeId checked once (bounding candidates is R5's job)")
        (is (zero? (:hits (s/stats cache))) "sq changed, so no executable is valid in root'")))))

(deftest r4-pinned-fibers-keep-their-verdicts
  (let [wo (world)
        old (w/fiber wo)
        cache (doto (s/make-cache) (s/install! (exe-for-f (w/basis old))))
        _ (d/define! wo '(def sq (fn [x] (* 10 x))))
        new (w/fiber wo)
        stop (atom false)
        writer (future (loop [i 0]
                         (when-not @stop
                           (d/define! wo (list 'def (symbol (str "noise" (mod i 5))) i))
                           (recur (inc i))))
                       :done)
        readers (vec (for [[fib expect] [[old 10] [new 31] [old 10] [new 31]]]
                       (future (s/with-cache cache
                                 (vec (for [_ (range 200)]
                                        (= expect (d/eval-in fib '(f 3)))))))))
        observed (mapv deref readers)]
    (reset! stop true)
    (is (= :done @writer))
    (is (every? true? (apply concat observed)) "old fibers get 10 (sq squares), new ones 31")
    (let [st (s/stats cache)]
      (is (= 400 (:hits st)) "every old-root entry used the executable")
      (is (= 400 (:fallbacks st)) "every new-root entry fell back")
      (is (<= 2 (:revalidations st) 8)
          "one verdict per pinned root (a few more if racing threads both computed one)"))
    (testing "raising the old fiber moves it to the edited root, where the verdict is invalid"
      (w/raise-basis! old)
      (is (= 31 (s/with-cache cache (d/eval-in old '(f 3)))) "the raised fiber sees the edited sq"))))
