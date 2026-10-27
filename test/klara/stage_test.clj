(ns klara.stage-test
  "The specialization cache: guards on entry with generic fallback,
  invalidation from recorded reads, certificate-checked install, and
  gate R3 (deleting all caches changes no result)."
  (:require [clojure.test :refer [deftest is testing]]
            [klara.world :as w]
            [klara.eval :as ev]
            [klara.defs :as d]
            [klara.stage :as s]))

(def definitions
  '[(def sq (fn [x] (* x x)))
    (def sum-sq (fn [xs] (reduce + (map sq xs))))
    (def pow (fn [n x] (if (zero? n) 1 (* x (pow (dec n) x)))))
    (defmacro twice [e] (qq (+ ~e ~e)))
    (def f (fn [y] (twice (sq y))))
    (def counter (fn [h n] (if (zero? n) 0 (+ (perform h :tick) (counter h (dec n))))))])

(def programs
  '[(sq 7)
    (sq 2.5)
    (sum-sq [1 2 3 4])
    (pow 3 2)
    ((specialize pow 2) 9)
    ((specialize pow 2) 1.5)
    (f 3)
    (try (sq "a") (catch Exception e :type-error))
    (handle [h {:tick (fn [k] (k 1))}] (counter h 5))
    (let [make (fn [n] (fn [x] (+ n (sq x))))] [((make 1) 2) ((make 2) 2)])])

(defn- world []
  (let [wo (w/make-world)]
    (doseq [df definitions] (d/define! wo df))
    wo))

(defn- results [root] (mapv #(d/eval-form root %) programs))

(defn- populate! [cache root]
  (doseq [sym '[sq sum-sq f counter]]
    (s/install! cache (s/residual (d/lookup root sym) root)))
  (let [sq (d/lookup root 'sq) pow (d/lookup root 'pow)]
    (s/install! cache (s/executable sq #{[:captures []] [:arg 0 :long]}
                                    (fn [x] (* x x)) {:author :test}))
    (s/install! cache (s/executable pow #{[:captures []] [:statics [2]] [:arg 0 :number]}
                                    (fn [x] (* x x)) {:author :test}))
    (s/install! cache (s/residual pow [3] root)))
  cache)

(deftest r3-deleting-caches-changes-no-result
  (let [wo (world)
        root (w/snapshot wo)
        generic (results root)
        cache (populate! (s/make-cache) root)
        cached (s/with-cache cache (results root))
        st (s/stats cache)]
    (is (= generic cached))
    (is (pos? (:hits st)) "executables did run")
    (is (pos? (:fallbacks st)) "and some guards failed: (sq 2.5), (sq \"a\")")
    (s/clear! cache)
    (is (empty? (s/executables cache)))
    (is (= generic (s/with-cache cache (results root))) "after deletion")
    (testing "after an edit, a stale cache still changes nothing"
      (let [cache (populate! (s/make-cache) root)]
        (d/define! wo '(def sq (fn [x] (+ x x))))
        (d/invalidate! wo 'sq)
        (let [root' (w/snapshot wo)
              generic' (results root')]
          (is (not= generic generic'))
          (is (= generic' (s/with-cache cache (results root'))))
          (is (pos? (s/invalidate! cache root')) "sweep drops entries whose reads broke")
          (is (= generic' (s/with-cache cache (results root'))))
          (is (= generic (s/with-cache cache (results root)))
              "the old root still gets old answers (surviving entries)"))))))

(deftest guards-on-entry
  (let [wo (world) root (w/snapshot wo)
        sq (d/lookup root 'sq)
        cache (s/make-cache)
        calls (atom 0)]
    (s/install! cache (s/executable sq #{[:captures []] [:arg 0 :long]}
                                    (fn [x] (swap! calls inc) (* x x)) {:author :test}))
    (s/with-cache cache
      (is (= 49 (d/eval-form root '(sq 7))))
      (is (= 6.25 (d/eval-form root '(sq 2.5)))))
    (is (= 1 @calls) "the :long guard admitted 7 and refused 2.5")
    (is (= {:hits 1 :fallbacks 1} (select-keys (s/stats cache) [:hits :fallbacks])))
    (testing "captures guard: same code, different captured values"
      (let [make (d/eval-form root '(fn [n] (fn [x] (+ n x))))
            c1 (make 1) c2 (make 2)
            cache (s/make-cache)]
        (s/install! cache (s/executable c1 #{[:captures [1]]} (fn [x] (+ 1 x)) {:author :test}))
        (s/with-cache cache (is (= [11 12] [(c1 10) (c2 10)])))
        (is (= {:hits 1 :fallbacks 1} (select-keys (s/stats cache) [:hits :fallbacks])))))))

(deftest invalidation-from-recorded-reads
  (let [wo (world) root (w/snapshot wo)
        cache (populate! (s/make-cache) root)
        n (count (s/executables cache))]
    (d/define! wo '(def pow (fn [n x] (if (zero? n) 1 (* x (pow (dec n) x))))))
    (is (zero? (s/invalidate! cache (w/snapshot wo))) "same code, same value id: nothing breaks")
    (d/define! wo '(def sq (fn [x] (* x x 1))))
    (let [dropped (s/invalidate! cache (w/snapshot wo))]
      (is (= 2 dropped) "sum-sq and f read sq; sq's own entries key on its old CodeId")
      (is (= (- n dropped) (count (s/executables cache)))))))

(deftest certificate-checked-install
  (let [wo (world) root (w/snapshot wo)
        sq (d/lookup root 'sq)
        good (s/executable sq #{[:captures []] [:arg 0 :long]} (fn [x] (* x x)) {:author :test})
        reason (fn [exe] (try (s/install! (s/make-cache) exe) :installed
                              (catch Exception e (:reason (ex-data e)))))]
    (is (= :installed (reason good)))
    (is (= :installed (reason (s/residual sq root))))
    (is (= :missing-certificate (reason (dissoc good :certificate))))
    (is (= :code-id-mismatch (reason (assoc good :code-id "deadbeef"))))
    (is (= :assumption-mismatch (reason (update good :guards disj [:arg 0 :long])))
        "dropping a guard after certification is caught")
    (is (= :untrusted-checker (reason (assoc-in good [:certificate :checker] :someone/else))))
    (is (= :missing-provenance (reason (update good :certificate dissoc :provenance))))
    (is (= :digest-mismatch (reason (-> good
                                        (assoc :code-id "x")
                                        (assoc-in [:certificate :code-id] "x")))))))
