(ns klara.bench
  "Performance comparison on shared programs (STATUS.md#performance):
  Klara interpreted, Klara compiled (optimize!), SCI and Clojure.

  Timing is best-of-N after warmup in one JVM: good enough to find cliffs
  and order-of-magnitude factors, not a publication benchmark. Run with
  clojure -M:bench."
  (:require [clojure.pprint :as pp]
            [klara.host.api :as k]
            [sci.core :as sci]))

(def programs
  ;; name, definitions, call; all three engines read the same source.
  [{:name :fib :defs "(defn fib [n] (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))" :call "(fib 20)"}
   {:name :loop :defs "(defn sum-to [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc i)) acc)))"
    :call "(sum-to 100000)"}
   {:name :closures :defs "(defn adders [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) ((fn [x] (+ x i)) acc)) acc)))"
    :call "(adders 50000)"}
   {:name :let-heavy :defs "(defn poly [n] (loop [i 0 acc 0] (if (< i n) (let [a (* i i) b (+ a 3) c (- b i)] (recur (inc i) (+ acc c))) acc)))"
    :call "(poly 50000)"}
   {:name :seq-ops :defs "(defn seqs [v] (reduce + 0 (map inc (filter odd? v))))" :call "(seqs (vec (range 20000)))"}
   {:name :maps :defs "(defn freq [n] (loop [i 0 m {}] (if (< i n) (recur (inc i) (update m (mod i 7) (fnil inc 0))) m)))"
    :call "(count (freq 20000))"}])

(defn- time-ms [f]
  (let [t (System/nanoTime)] (f) (/ (- (System/nanoTime) t) 1e6)))

(defn- best [f n]
  (dotimes [_ 3] (f))
  (apply min (repeatedly n #(time-ms f))))

(defn- klara-engine [compiled?]
  (fn [{:keys [defs call name]}]
    (let [s (k/session {:roots ["lib"] :out (java.io.StringWriter.)})]
      (k/eval-string s (str "(ns b (:require [klara.compiler :as compiler]))\n" defs))
      (when compiled?
        (doseq [q (re-seq #"(?<=\(defn )[a-z-]+" defs)]
          (k/eval-string s (str "(compiler/optimize! 'b/" q ")"))))
      #(k/eval-string s call))))

(defn- sci-engine [{:keys [defs call]}]
  (let [ctx (sci/init {})]
    (sci/eval-string* ctx defs)
    #(sci/eval-string* ctx call)))

(defn- clojure-engine [{:keys [defs call]}]
  (let [n (create-ns (gensym "bench"))]
    (binding [*ns* n] (refer 'clojure.core) (load-string defs))
    #(binding [*ns* n] (load-string call))))

(def engines
  {:klara (klara-engine false) :klara-compiled (klara-engine true) :sci sci-engine :clojure clojure-engine})

(defn run
  ([] (run (map :name programs)))
  ([names]
   (vec (for [p programs :when (some #{(:name p)} names)]
          (into {:program (:name p)}
                (for [[e mk] engines]
                  [e (try (let [f (mk p)] (Math/round (* 100 (best f 7))))
                          (catch Throwable ex (str "error: " (.getMessage ex))))]))))))

(defn -main [& _]
  (let [r (run)]
    (println "times in hundredths of a millisecond (best of 7)")
    (pp/print-table [:program :klara :klara-compiled :sci :clojure] r)))
