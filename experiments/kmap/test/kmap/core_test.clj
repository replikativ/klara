(ns kmap.core-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.generators :as gen]
            [clojure.walk :as walk]
            [kmap.core :as k]
            [kmap.gen :as g :refer [->R]]))

(def ^:dynamic *num-tests* 10000)

(defn- variants
  "The plain map m and several KMap renderings of the same tree."
  [t bits]
  (let [m (k/deep-clj t)]
    {:m m
     :km-top (k/kmap m)              ; only top level is a KMap
     :km-deep (k/deep-kmap t)        ; every nested map is a KMap
     :km-mix (let [x (g/mix-convert t bits)] (if (k/kmap? x) x (k/kmap x)))}))

(defn- jequals-contract [a b]
  ;; .equals symmetric, and .equals => equal .hashCode
  (let [ab (.equals ^Object a b) ba (.equals ^Object b a)]
    (and (= ab ba)
         (or (not ab) (= (.hashCode ^Object a) (.hashCode ^Object b))))))

(defn- eq-props
  "Everything that must hold between a KMap rendering km and the plain map m
  of the same tree."
  [km m]
  {:eq-km-m      (= km m)
   :eq-m-km      (= m km)
   :hash         (= (hash km) (hash m))
   :hash-spec    (= (hash km) (hash-unordered-coll (or (seq km) ())))
   :set-member   (and (contains? #{m} km) (contains? #{km} m)
                      (contains? (hash-set m) km) (contains? (hash-set km) m))
   :map-member   (and (= 1 (get {m 1} km)) (= 1 (get {km 1} m))
                      (= 1 (get (hash-map m 1) km)) (= 1 (get (hash-map km 1) m)))
   :jequals      (and (.equals ^Object km m) (.equals ^Object m km))
   :jhashcode    (= (.hashCode ^Object km) (.hashCode ^Object m))
   ;; pr-str is order-dependent: a PHM-delegate KMap and a PAM-backed m
   ;; that are = may print in different orders (as PAM vs PHM do in
   ;; Clojure). So: KMap prints exactly as its delegate, and reads back =.
   :pr-str       (and (or (not= k/*backend* :phm) (= (pr-str km) (pr-str (k/delegate km))))
                      (= (read-string (pr-str km)) m)
                      ;; same order as PHM only when the delegate IS a PHM
                      (or (not= k/*backend* :phm)
                          (= (pr-str (k/kmap (into clojure.lang.PersistentHashMap/EMPTY m)))
                             (pr-str (into clojure.lang.PersistentHashMap/EMPTY m)))))
   :str          (= (str km) (pr-str km))
   :nested-in-clj (and (= {:x km} {:x m}) (= {:x m} {:x km})
                       (= [km] [m]) (= #{km} #{m})
                       (= (hash {:x km}) (hash {:x m}))
                       (= (hash [km]) (hash [m])))
   :clj-in-kmap  (and (= (k/kmap {:x m}) {:x km}) (= {:x km} (k/kmap {:x m}))
                      (= (hash (k/kmap {:x m})) (hash {:x km})))
   :record-field (and (= (->R km) (->R m)) (= (hash (->R km)) (hash (->R m))))})

(defn- first-failure [props] (some (fn [[k v]] (when-not v k)) props))

(def prop-equality
  (prop/for-all [[t _ bits] g/gen-case]
    (let [{:keys [m] :as vs} (variants t bits)]
      (every? (fn [kk]
                (let [p (eq-props (vs kk) m)]
                  (or (nil? (first-failure p))
                      (do (println "FAIL" kk (first-failure p) (pr-str m)) false))))
              [:km-top :km-deep :km-mix]))))

(def prop-relational
  ;; For a second map m2 (numeric retype of the tree), KMap answers must
  ;; equal PHM answers for =, .equals and hash consistency, in both orders.
  (prop/for-all [[t choice bits] g/gen-case]
    (let [{:keys [m km-deep km-mix]} (variants t bits)
          m2 (k/deep-clj (g/retype t choice))
          km2 (k/deep-kmap m2)
          base (= m m2)
          jbase (.equals ^Object m m2)]
      (and (every? #(= base %) [(= km-deep m2) (= m2 km-deep) (= km-mix m2) (= m2 km-mix)
                                (= km-deep km2) (= km2 km-deep) (= m km2) (= km2 m)])
           (every? #(= jbase %) [(.equals ^Object km-deep m2) (.equals ^Object m2 km-deep)
                                 (.equals ^Object km-deep km2)])
           ;; = implies equal hash (on both representations)
           (or (not base) (= (hash km-deep) (hash m2) (hash km2) (hash m)))
           (jequals-contract km-deep m2)
           (jequals-contract km-deep km2)
           (jequals-contract m m2)))))

(defn- rkv-set [m] (set (reduce-kv (fn [a kk v] (conj a [kk v])) [] m)))

(defn ops-checks [[t choice bits] extra v]
    (let [{:keys [m km-mix]} (variants t bits)
          km km-mix
          m2 (k/deep-clj (g/retype t choice))
          ks (concat (take 2 (keys m)) (keys extra))
          k1 (first (keys m))
          checks
          {:count     (= (count km) (count m))
           :get       (every? #(= (get km %) (get m %)) ks)
           :get-nf    (every? #(= (get km % ::nf) (get m % ::nf)) ks)
           :invoke    (every? #(= (km % ::nf) (m % ::nf)) ks)
           :kw        (and (= (:a km) (:a m)) (= (:b km ::nf) (:b m ::nf)))
           :contains  (every? #(= (contains? km %) (contains? m %)) ks)
           :find      (every? #(= (find km %) (find m %)) ks)
           :assoc     (let [r (assoc km :zz v)] (and (k/kmap? r) (= r (assoc m :zz v))))
           :dissoc    (let [r (apply dissoc km ks)] (and (k/kmap? r) (= r (apply dissoc m ks))))
           :conj      (and (= (conj km [:q v]) (conj m [:q v]))
                           (= (conj km extra) (conj m extra))
                           (= (conj km (first extra)) (conj m (first extra)))
                           (= (conj km nil) m))
           :merge     (let [r (merge km extra m2)]
                        (and (k/kmap? r) (= r (merge m extra m2))
                             (= (merge extra km) (merge extra m))
                             (= (merge m2 km) (merge m2 m))))
           :select-keys (= (select-keys km ks) (select-keys m ks))
           :update-in (or (nil? k1)
                          (and (= (update-in km [k1] (fn [x] [x])) (update-in m [k1] (fn [x] [x])))
                               (or (not (or (map? (get m k1)) (nil? (get m k1))))
                                   (= (update-in km [k1 :deep] (fnil inc 0))
                                      (update-in m [k1 :deep] (fnil inc 0))))))
           :frequencies (= (frequencies [km m m2 km]) (frequencies [m m m2 m]))
           :distinct  (= (count (distinct [km m])) 1)
           :group-by  (= (group-by identity [km m]) (group-by identity [m m]))
           :into-clj  (= (into {} km) m)
           :into-km   (let [r (into km m2)] (and (k/kmap? r) (= r (into m m2))))
           :into-empty (= (into (empty km) (seq m)) m)
           :empty     (and (k/kmap? (empty km)) (= (empty km) {}) (= {} (empty km)))
           :reduce-kv (= (rkv-set km) (rkv-set m))
           :reduce    (= (set (reduce conj [] km)) (set (reduce conj [] m)))
           :reduced   (let [r (reduce-kv (fn [_ kk _] (reduced [kk])) ::none km)
                              r2 (reduce (fn [_ e] (reduced e)) ::none km)]
                          (if (empty? m) (= r r2 ::none)
                              (and (contains? m (first r)) (contains? (set m) r2))))
           :keys-vals (and (= (frequencies (keys km)) (frequencies (keys m)))
                           (= (frequencies (vals km)) (frequencies (vals m))))
           :seq       (= (frequencies (seq km)) (frequencies (seq m)))
           :iter      (= (frequencies (iterator-seq (.iterator ^Iterable km)))
                         (frequencies (iterator-seq (.iterator ^Iterable m))))
           :transient (let [f (fn [x] (persistent!
                                       (reduce (fn [tr [kk vv]] (dissoc! (assoc! tr kk vv) :a))
                                               (transient x) (concat extra (seq m2)))))
                            r (f km)]
                        (and (k/kmap? r) (= r (f m))))
           :transient-lookup (let [tr (transient km)]
                               (every? #(= (get tr % ::nf) (get m % ::nf)) ks))
           :destructure (let [{a :a b :b x k1 :or {b ::dflt} :as all} km
                              {a' :a b' :b x' k1 :or {b' ::dflt} :as all'} m]
                          (and (= [a b x] [a' b' x']) (identical? all km) (= all all')))
           :destructure-kwargs (let [f (fn [& {:keys [a b] :as opts}] [a b opts])]
                                 (= (f km) (f m)))
           :jmap      (and (= (.size ^java.util.Map km) (.size ^java.util.Map m))
                           (= (set (.keySet ^java.util.Map km)) (set (.keySet ^java.util.Map m)))
                           (= (set (.entrySet ^java.util.Map km)) (set (.entrySet ^java.util.Map m)))
                           (= (.entrySet ^java.util.Map km) (.entrySet ^java.util.Map m))
                           (= (.keySet ^java.util.Map km) (.keySet ^java.util.Map m))
                           (every? #(= (.containsValue ^java.util.Map km %)
                                       (.containsValue ^java.util.Map m %)) (vals m)))
           :hashmap-copy (let [hm (java.util.HashMap. ^java.util.Map km)]
                           (and (= hm (java.util.HashMap. ^java.util.Map m))
                                (.equals ^Object km hm) (.equals ^Object hm km)))
           :meta      (let [r (with-meta km {:x 1})]
                        (and (= r km) (= (hash r) (hash km)) (= {:x 1} (meta r))
                             (= {:x 1} (meta (assoc r :zz 1)))
                             (= {:x 1} (meta (empty r)))))
           :postwalk  (let [r (walk/postwalk identity km)]
                        (and (= r m) (= (walk/postwalk identity m) r)))
           :map?      (and (map? km) (coll? km) (not (record? km)) (not (sequential? km)))}]
      checks))

(def prop-ops
  (prop/for-all [c g/gen-case
                 extra (gen/map g/gen-key g/gen-scalar {:max-elements 4})
                 v gen/small-integer]
    (let [checks (ops-checks c extra v)]
      (or (nil? (first-failure checks))
          (do (println "OPS FAIL" (first-failure checks)) false)))))

(def prop-records-never-equal
  ;; A record with the same entries is never = to a map; same for KMap.
  (prop/for-all [s g/gen-scalar]
    (let [r (->R s) m {:a s} km (k/kmap m)]
      (and (= (= r m) (= r km) false)
           (= (= m r) (= km r) false)))))

(defn run [p n & [label]]
  (let [r (tc/quick-check n p :max-size 60 :seed (System/currentTimeMillis))]
    (println "quick-check" label (select-keys r [:pass? :num-tests :seed :time-elapsed-ms])
             (if (:pass? r) "" (pr-str (:smallest (:shrunk r)))))
    r))

(deftest equality-props   (is (true? (:pass? (run prop-equality *num-tests* :equality)))))
(deftest relational-props (is (true? (:pass? (run prop-relational *num-tests* :relational)))))
(deftest ops-props        (is (true? (:pass? (run prop-ops *num-tests* :ops)))))
(deftest record-props     (is (true? (:pass? (run prop-records-never-equal 2000 :records)))))

(deftest unit-cases
  (testing "conj arg shapes and errors match Clojure"
    (is (thrown-with-msg? IllegalArgumentException #"pair" (conj (k/kmap) [1 2 3])))
    (is (thrown? RuntimeException (.assocEx ^clojure.lang.IPersistentMap (k/kmap {1 2}) 1 3))))
  (testing "java.util.Map mutators throw"
    (is (thrown? UnsupportedOperationException (.put ^java.util.Map (k/kmap) 1 2)))
    (is (thrown? UnsupportedOperationException (.clear ^java.util.Map (k/kmap {1 2})))))
  (testing "identity preserved on no-op assoc/dissoc"
    (let [km (k/kmap {:a 1})]
      (is (identical? km (assoc km :a 1)))
      (is (identical? km (dissoc km :b)))))
  (testing "transient used after persistent! throws"
    (let [t (transient (k/kmap))]
      (persistent! t)
      (is (thrown? IllegalAccessError (assoc! t 1 2)))))
  (testing "NaN: KMap agrees with PHM (both false for distinct maps)"
    (let [m {:a ##NaN} km (k/kmap m)]
      (is (= (= m {:a ##NaN}) (= km {:a ##NaN})))
      (is (= (= m km) (= km m)))))
  (testing "-0.0 vs 0.0"
    (is (= (k/kmap {:a 0.0}) {:a -0.0}))
    (is (= (hash (k/kmap {:a 0.0})) (hash {:a -0.0})))))
