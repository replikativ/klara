(ns klara.bench
  "Performance comparison on shared programs (STATUS.md#performance):
  Klara interpreted, Klara compiled (optimize!), SCI and Clojure.

  Timing is best-of-N after a warmup of 20 calls or 2 s in one JVM: good enough to find cliffs
  and order-of-magnitude factors, not a publication benchmark. Run with
  clojure -M:bench."
  (:require [clojure.pprint :as pp]
            [klara.host.api :as k]
            [sci.core :as sci]))

(def ^:private SMC-PLAIN
  "(defn smc-plain [ys n seed]
  (let [M 2147483647
        next-key (fn [key] (mod (* 48271 key) M))
        split-key (fn [key i] (next-key (mod (+ (* 1000003 key) i 1) M)))
        uniform (fn [key] (/ (double key) M))
        emission (fn [p n] (loop [i n q 0.5] (if (> i 0) (recur (dec i) (/ (+ q p) 2.0)) q)))]
    (loop [ps (mapv (fn [i] (let [key (next-key (split-key seed i))] {:x (< (uniform key) 0.5) :key key})) (range n))
           obs ys key seed z 1.0]
      (if (empty? obs)
        [(count (filter :x ps)) z]
        (let [weighted (mapv (fn [p] (let [q (emission (if (:x p) 0.9 0.2) 16)] (assoc p :w (if (first obs) q (- 1.0 q))))) ps)
              total (reduce + (map :w weighted))
              key2 (next-key key)
              kids (loop [j 0 i 0 acc (:w (first weighted)) out []]
                     (if (= j n) out
                         (if (< acc (* (/ (+ (uniform key2) j) n) total))
                           (recur j (inc i) (+ acc (:w (nth weighted (inc i)))) out)
                           (recur (inc j) i acc (conj out (nth weighted i))))))
              children (mapv (fn [i p] (let [split (split-key (:key p) i)
                                             draw (if (next obs) (next-key split) split)]
                                         {:key draw :x (if (next obs) (< (uniform draw) (if (:x p) 0.8 0.2)) (:x p))}))
                             (range n) kids)]
          (recur children (next obs) key2 (* z (/ total n))))))))
(def ys [true true false true false true false false true true true false])")

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
    :call "(count (freq 20000))"}
   ;; closures passed to host higher-order functions (each call is a host callback)
   {:name :hof :defs "(defn hof [v] (reduce (fn [a x] (+ a x)) 0 (map (fn [x] (* 2 x)) (filter (fn [x] (odd? x)) v))))"
    :call "(hof (vec (range 20000)))"}
   ;; calls with several arguments building and reading maps
   {:name :records :defs "(defn mk [a b c] {:a a :b b :c c}) (defn rec [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (:b (mk i (inc i) (dec i))))) acc)))"
    :call "(rec 20000)"}
   ;; sequential Monte Carlo written as a state machine (test/klara/showcase_test.clj)
   {:name :smc-plain :defs SMC-PLAIN :call "(smc-plain ys 32 42)"}
   ;; Klara with effects; SCI and Clojure, which have no handlers, run the plain twin.
   ;; The SMC of showcases/smc.clj with multi-shot continuations:
   {:name :smc-effects :twin true
    :klara-defs "(require 'showcases.smc)" :klara-call "(showcases.smc/smc showcases.smc/ys 32 42)"
    :defs SMC-PLAIN :call "(smc-plain ys 32 42)"}
   ;; a generator: one effect per iteration, handled tail-resumptively; twin: a function call
   {:name :generator :twin true
    :klara-defs "(defn gen [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (perform :next i))) acc))) (defn run-gen [n] (handle {:next (fn [k x] (k (* 2 x)))} (gen n)))"
    :klara-call "(run-gen 20000)"
    :defs "(defn nxt [x] (* 2 x)) (defn gen [n] (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (nxt i))) acc)))" :call "(gen 20000)"}
   ;; enumeration by a multi-shot handler (each flip resumed twice); twin: plain recursion
   {:name :multishot :twin true
    :klara-defs "(defn tree [d] (if (= d 0) 1 (if (perform :flip) (tree (dec d)) (+ 1 (tree (dec d)))))) (defn enum [d] (handle {:flip (fn [k] (+ (k true) (k false)))} (tree d)))"
    :klara-call "(enum 12)"
    :defs "(defn enum [d] (if (= d 0) 1 (+ (enum (dec d)) (+ (enum (dec d)) (bit-shift-left 1 (dec d))))))" :call "(enum 12)"}])

(defn- time-ms [f]
  (let [t (System/nanoTime)] (f) (/ (- (System/nanoTime) t) 1e6)))

(defn- best
  "Best of n after warming up for 20 calls or two seconds, whichever is longer."
  [f n]
  (let [t0 (System/nanoTime)]
    (loop [i 0] (when (or (< i 20) (< (- (System/nanoTime) t0) 2e9)) (f) (recur (inc i)))))
  (apply min (repeatedly n #(time-ms f))))

(defn- klara-engine [compiled?]
  (fn [{:keys [defs call klara-defs klara-call]}]
    (let [s (k/session {:roots ["lib" "."] :out (java.io.StringWriter.)})
          defs (or klara-defs defs) call (or klara-call call)]
      (k/eval-string s (str "(ns b (:require [klara.compiler :as compiler] [klara.effect :refer [perform handle]]))\n" defs))
      (when compiled?
        ;; definitions the backend does not compile (L4.lower.subset) stay interpreted
        (doseq [q (concat (re-seq #"(?<=\(defn )[a-z-]+" defs)
                          (when (re-find #"showcases.smc" defs) '[emission smc resample next-key split-key uniform resume]))]
          (k/eval-string s (str "(compiler/optimize! '" (if (re-find #"showcases.smc" defs) "showcases.smc/" "b/") q ")"))))
      #(k/eval-string s (str "(klara.profile/without (fn [] " call "))")))))

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
          (into {:program (cond-> (:name p) (:twin p) (-> name (str " (twin)") keyword))}
                (for [[e mk] engines]
                  [e (try (let [f (mk p)] (Math/round (* 100 (best f 7))))
                          (catch Throwable ex (str "error: " (.getMessage ex))))]))))))

(defn -main [& _]
  (let [r (run)]
    (println "times in hundredths of a millisecond (best of 7); (twin): Klara runs the effectful")
    (println "program, SCI and Clojure a plain one computing the same result")
    (pp/print-table [:program :klara :klara-compiled :sci :clojure :klara/sci] 
                    (map #(assoc % :klara/sci (when (and (number? (:klara %)) (number? (:sci %)) (pos? (:sci %)))
                                                 (format "%.1f" (/ (double (:klara %)) (:sci %))))) r))))
