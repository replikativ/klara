(ns interpreter.run
  "Paired generic-driver measurements; no Klara compiler hooks."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.core :as core] [klara.eval :as ev]
            [klara.expand :as x] [klara.world :as w])
  (:import [java.lang.management ManagementFactory]
           [com.sun.management ThreadMXBean]))

(def workloads
  [{:name :sum :n 1000
    :form '(fn [n] (loop [i 0 sum 0] (if (< i n) (recur (inc i) (+ sum i)) sum)))}
   {:name :calls :n 1000
    :form '(let [f (fn [x] (+ x 1))]
             (fn [n] (loop [i 0 sum 0] (if (< i n) (recur (inc i) (+ sum (f i))) sum))))}
   {:name :persistent-update :n 1000
    :form '(fn [n] (loop [i 0 acc [0 0]]
                    (if (< i n) (recur (inc i) (assoc acc 0 (+ (nth acc 0) i) 1 (inc (nth acc 1)))) acc)))}
   {:name :host-callback :n 1000
    :form '(fn [n] (reduce + 0 (map (fn [x] (* x x)) (range n))))}
   {:name :handler :n 100
    :form '(fn [n]
             (handle [h {:tick (fn [x k] (k (inc x)))}]
               (loop [i 0 sum 0]
                 (if (< i n) (recur (inc i) (+ sum (perform h :tick i))) sum))))}
   {:name :multi-shot :n 100
    :form '(fn [n]
             (loop [i 0 sum 0]
               (if (< i n)
                 (let [pair (handle [h {:pick (fn [k] [(k 1) (k 2)])}]
                              (+ i (perform h :pick)))]
                   (recur (inc i) (+ sum (first pair) (second pair)))) sum)))}
   {:name :exceptions :n 100
    :form '(fn [n]
             (loop [i 0 sum 0]
               (if (< i n)
                 (recur (inc i) (+ sum (try (/ 1 (mod i 7)) (catch ArithmeticException e 0)))) sum)))}
   {:name :staging :n 10
    :form '(fn [n]
             (loop [i 0 sum 0]
               (if (< i n)
                 (let [f (run (code (fn [x] (+ x (esc (lift i))))))]
                   (recur (inc i) (+ sum (f i)))) sum)))}])

(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))

(defn measure [^ThreadMXBean bean f n]
  (let [tid (.threadId (Thread/currentThread)) sink (volatile! nil)
        allocated (.getThreadAllocatedBytes bean tid) start (System/nanoTime)]
    (dotimes [_ 5] (vreset! sink (f n)))
    {:ns-per-call (/ (- (System/nanoTime) start) 5.0)
     :bytes-per-call (/ (- (.getThreadAllocatedBytes bean tid) allocated) 5.0)
     :value @sink}))

(defn benchmark [workload process]
  (let [{:keys [name form n]} workload
        f (ev/run (x/expand-expr form w/empty-root))
        expected (binding [ev/*reference-driver* true] (f n))
        bean ^ThreadMXBean (ManagementFactory/getThreadMXBean)
        _ (assert (.isThreadAllocatedMemorySupported bean))
        _ (.setThreadAllocatedMemoryEnabled bean true)
        ;; Alternate warmup and sample order; process parity changes who starts.
        order (if (even? process) [true false] [false true])
        _ (dotimes [_ 40]
            (doseq [reference? order]
              (binding [ev/*reference-driver* reference?] (assert (= expected (f n))))))
        pairs (mapv (fn [i]
                      (into {} (for [reference? (if (even? i) order (reverse order))]
                                 [reference? (binding [ev/*reference-driver* reference?]
                                               (measure bean f n))]))) (range 9))]
    (assert (every? #(= expected (:value %)) (mapcat vals pairs)))
    {:workload name :n n :expected expected
     :engines (into {} (for [[key reference?] [[:reference true] [:fused false]]
                            :let [samples (mapv #(get % reference?) pairs)]]
                        [key {:median-ns (median (map :ns-per-call samples))
                              :median-bytes (median (map :bytes-per-call samples))
                              :samples samples}]))}))

(defn -main [& [process]]
  (let [process (Long/parseLong (or process "0"))]
    (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
      (let [rows (mapv #(benchmark % process) workloads)
            source-files (concat ["deps.edn" "experiments/interpreter/run.clj"]
                                 (map str (filter #(.isFile %) (file-seq (io/file "src")))))
            report {:process process :java (System/getProperty "java.runtime.version")
                    :clojure (clojure-version) :compiler-cache false
                    :jvm-arguments (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
                    :os {:name (System/getProperty "os.name") :arch (System/getProperty "os.arch")
                         :version (System/getProperty "os.version")
                         :available-processors (.availableProcessors (Runtime/getRuntime))}
                    :measurement {:warmup-calls-per-driver 40 :samples 9 :calls-per-sample 5
                                  :order :alternating :allocation :current-thread-only}
                    :limits [:one-machine :not-guaranteed-steady-state :preparation-excluded
                             :no-retained-memory-or-GC-attribution :generic-interpreter-only]
                    :source-sha256 (into {} (map (fn [p] [p (core/sha256 (slurp p))]) source-files))
                    :rows rows}
            output (str "target/interpreter/process-" process ".edn")]
        (io/make-parents output)
        (spit output (with-out-str (pp/pprint report)))
        (doseq [row rows]
          (println (:workload row)
                   (into {} (map (fn [[engine data]] [engine (select-keys data [:median-ns :median-bytes])]))
                         (:engines row))))
        (println :report output)))
    (shutdown-agents)))
