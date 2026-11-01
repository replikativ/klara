(ns klara.awfy
  "Are We Fast Yet? benchmarks (design/07-performance.md): each plain-Clojure
  file in bench/awfy runs on Clojure, on the Klara interpreter and on Klara
  after the investor has looked at it; bench/awfy/js runs on node (V8).
  Each measurement runs the benchmark until a second has passed and reports
  the mean of the second half, in milliseconds.

    clojure -M:awfy"
  (:require [clojure.data.json :as json]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [klara.host.api :as k]))

(def benchmarks ["mandelbrot" "sieve" "towers" "list"])

(defn- measure [f]
  (let [start (System/nanoTime)
        times (loop [ts []]
                (if (< (- (System/nanoTime) start) 1000000000)
                  (let [t (System/nanoTime)] (f) (recur (conj ts (/ (- (System/nanoTime) t) 1e6))))
                  ts))
        half (drop (quot (count times) 2) times)]
    (/ (reduce + half) (count half))))

(defn- clojure-run [b]
  (load-file (str "bench/awfy/" b ".clj"))
  (let [run @(resolve (symbol (str "awfy." b) "run"))
        expected @(resolve (symbol (str "awfy." b) "expected"))]
    {:ok (= expected (run)) :ms (measure run)}))

(defn- batched
  "ms per evaluation of Klara expression `body`, run in batches inside one
   evaluation (an eval-string costs far more than a small benchmark), minus
   the same loop with an empty body."
  [call body]
  (let [per (fn [body n]
              (let [t (System/nanoTime)]
                (call (str "(loop [i 0] (when (< i " n ") " body " (recur (inc i))))"))
                (/ (- (System/nanoTime) t) 1e6 n)))
        ;; a batch of at least 20 ms
        n (loop [n 1] (if (or (>= (* n (per body n)) 20) (> n 1000000)) n (recur (* 2 n))))
        series (fn [body] (let [start (System/nanoTime)]
                            (loop [ts []]
                              (if (< (- (System/nanoTime) start) 1000000000)
                                (recur (conj ts (per body n)))
                                (let [half (drop (quot (count ts) 2) ts)] (/ (reduce + half) (count half)))))))]
    (- (series body) (series "nil"))))

(defn- klara-run [b]
  (let [s (k/session {:roots ["lib" "bench"] :out (java.io.StringWriter.)})
        ns-sym (symbol (str "awfy." b))
        call (fn [src] (k/eval-string s (str "(ns klara-awfy-" b " (:require [" ns-sym " :as b] [klara.investor :as investor]))" src)))
        ok (try (= (call "(b/run)") (call "b/expected")) (catch Throwable e (str "fails: " (.getMessage e))))]
    (if (string? ok)
      {:ok ok}
      (let [interpreted (batched call "(b/run)")
            decisions (call (str "(mapv (juxt :name :decision :chosen) (investor/invest! '" ns-sym "))"))
            ;; from here on the investor also runs between forms (L4.jit.trigger)
            _ (k/automatic-investor! s)
            _ (dotimes [_ 3] (batched call "(b/run)"))
            ;; each definition's latest decision
            decisions (call "(mapv (fn [[q ds]] (let [d (peek ds)] [q (:decision d) (:chosen d)])) investor/decisions)")
            ok-after (= (call "(b/run)") (call "b/expected"))
            compiled (batched call "(b/run)")]
        {:ok (and ok ok-after) :interpreted-ms interpreted :ms compiled
         :decisions (into {} (map (fn [[q d c]] [(name q) (if c (str (name d) " " (name c)) (name d))]) decisions))}))))

(defn -main [& names]
  (let [node (try (json/read-str (:out (sh/sh "node" "bench/awfy/js/benchmarks.js")) :key-fn keyword)
                  (catch Throwable _ nil))
        rows (for [b (or (seq names) benchmarks)]
               (let [c (clojure-run b) kl (klara-run b) js (get node (keyword b))]
                 {:benchmark b :node-ms (:ms js) :clojure-ms (:ms c)
                  :klara-interpreted-ms (:interpreted-ms kl) :klara-ms (:ms kl)
                  :ok (and (:ok js) (:ok c) (true? (:ok kl))) :klara (:ok kl) :decisions (:decisions kl)}))]
    (doseq [r rows] (prn r))
    (shutdown-agents)))
