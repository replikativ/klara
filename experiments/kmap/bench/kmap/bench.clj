(ns kmap.bench
  "Criterium benchmarks: KMap (PHM delegate) vs PersistentHashMap."
  (:require [criterium.core :as crit]
            [clojure.walk :as walk]
            [kmap.core :as k]))

(set! *warn-on-reflection* true)

(defn- mean-ns [r] (* 1e9 (first (:mean r))))

(defmacro bench [expr]
  `(mean-ns (crit/quick-benchmark ~expr {})))

(defn build [n]
  (let [ks (mapv #(keyword (str "k" %)) (range n))
        phm (apply hash-map (interleave ks (range n)))
        phm2 (apply hash-map (interleave (reverse ks) (reverse (range n))))
        rnd (java.util.Random. 42)
        probe (object-array (repeatedly 8 #(nth ks (.nextInt rnd n))))]
    {:n n :ks ks :probe probe
     :phm phm :phm2 phm2
     :km (k/kmap phm) :km2 (k/kmap phm2)
     :ch (binding [k/*backend* :champ] (k/kmap phm))
     :ch2 (binding [k/*backend* :champ] (k/kmap phm2))}))

(defn- get8 ^long [m ^objects probe]
  (loop [i 0 acc 0]
    (if (< i 8) (recur (inc i) (+ acc (long (get m (aget probe i))))) acc)))

(defn- assoc8 [m ^objects probe]
  (loop [i 0 m m]
    (if (< i 8) (recur (inc i) (assoc m (aget probe i) -1)) m)))

(defn- sum-kv ^long [m] (reduce-kv (fn [^long a _ v] (+ a (long v))) 0 m))

(defn- kw8 ^long [m]
  ;; 8 keyword call sites; :k0..:k7 exist for n >= 8
  (+ (long (:k0 m)) (long (:k1 m)) (long (:k2 m)) (long (:k3 m))
     (long (:k4 m)) (long (:k5 m)) (long (:k6 m)) (long (:k7 m))))

(defn tree
  "Nested maps, branching b, depth d; leaves are longs. Nodes ~ b^d."
  [b d]
  (if (zero? d) d
      (into (hash-map) (map (fn [i] [(keyword (str "c" i)) (tree b (dec d))])) (range b))))

(defn count-nodes [t] (count (tree-seq map? vals t)))

(def ops
  [[:get        (fn [{:keys [probe]} m _] (bench (get8 m probe)))]
   [:assoc      (fn [{:keys [probe]} m _] (bench (assoc8 m probe)))]
   [:reduce-kv  (fn [_ m _] (bench (sum-kv m)))]
   [:into-clj   (fn [_ m _] (bench (into {} m)))]
   [:into-same  (fn [_ m _] (bench (into (empty m) m)))]
   [:equiv      (fn [_ m m2] (bench (= m m2)))]
   [:hash-cached (fn [_ m _] (bench (hash m)))]
   [:assoc+hash (fn [{:keys [probe]} m _] (bench (hash (assoc m (aget ^objects probe 0) -2))))]
   [:kw-lookup  (fn [_ m _] (bench (kw8 m)))]])

(declare main-interleaved)

(def ^:dynamic *rounds* 3)

(defn- measure
  "Interleave PHM / KMap / CHAMP-KMap for *rounds* rounds; keep each one's
  minimum mean (machine is shared, min is the least-disturbed estimate)."
  [thunks]
  (let [res (vec (repeat (count thunks) Double/MAX_VALUE))]
    (reduce (fn [res _] (mapv (fn [best t] (min best (t))) res thunks))
            res (range *rounds*))))

(defn- line [label n op [phm km ch]]
  (println (format "n=%-6s %-12s PHM %11.1f ns  KMap %11.1f ns  x%.3f   CHAMP %11.1f ns  x%.3f"
                   n (name op) phm km (/ km phm) ch (/ ch phm)))
  (flush)
  {:n n :op op :phm-ns phm :kmap-ns km :champ-ns ch :kmap-ratio (/ km phm) :champ-ratio (/ ch phm)})

(defn run-maps [ns-sizes out]
  (let [rows (atom [])]
    (doseq [n ns-sizes
            :let [d (build n)]
            [op f] ops]
      (swap! rows conj
             (line "" n op (measure [#(f d (:phm d) (:phm2 d))
                                     #(f d (:km d) (:km2 d))
                                     #(f d (:ch d) (:ch2 d))]))))
    (let [t (tree 10 4) kt (k/deep-kmap t)
          ct (binding [k/*backend* :champ] (k/deep-kmap t))
          _ (assert (= t kt ct))]
      (swap! rows conj
             (line "" (count-nodes t) :postwalk
                   (measure [#(bench (walk/postwalk identity t))
                             #(bench (walk/postwalk identity kt))
                             #(bench (walk/postwalk identity ct))]))))
    (spit out (pr-str @rows))
    @rows))

(defn run-isolated
  "One implementation per JVM (no cross-type JIT profile pollution).
  impl is :phm, :kmap or :champ. Appends rows to out."
  [impl ns-sizes out]
  (let [pick (fn [d] (case impl :phm [(:phm d) (:phm2 d)] :kmap [(:km d) (:km2 d)]
                       :champ [(:ch d) (:ch2 d)]))]
    (doseq [n ns-sizes
            :let [d (build n) [m m2] (pick d)]
            [op f] ops]
      (let [t (apply min (repeatedly 2 #(f d m m2)))]
        (println (format "%-6s n=%-6d %-12s %11.1f ns" (name impl) n (name op) t)) (flush)
        (spit out (str (pr-str {:impl impl :n n :op op :ns t}) "\n") :append true)))
    (let [t (tree 10 4)
          x (case impl :phm t :kmap (k/deep-kmap t)
                  :champ (binding [k/*backend* :champ] (k/deep-kmap t)))
          ns (apply min (repeatedly 2 #(bench (walk/postwalk identity x))))]
      (println (format "%-6s postwalk %d nodes %11.1f ns" (name impl) (count-nodes t) ns))
      (spit out (str (pr-str {:impl impl :n (count-nodes t) :op :postwalk :ns ns}) "\n") :append true))))

(defn -main [& [mode impl]]
  (if (= mode "isolated")
    (do (run-isolated (keyword impl) [8 1000 100000] "results/bench-maps-isolated.edn")
        (shutdown-agents))
    (main-interleaved)))

(defn main-interleaved []
  (println "load average at start:" (first (java.nio.file.Files/readAllLines (java.nio.file.Paths/get "/proc/loadavg" (into-array String [])))))
  (run-maps [8 1000 100000] "results/bench-maps.edn")
  (println "load average at end:" (first (java.nio.file.Files/readAllLines (java.nio.file.Paths/get "/proc/loadavg" (into-array String [])))))
  (shutdown-agents))
