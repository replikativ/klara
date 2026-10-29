(ns klara.pldi.worker
  (:require [clojure.string :as str] [clojure.java.io :as io]
            [klara.pldi.smc :as smc]
            [klara.compile-bench :as bench]
            [klara.compile.core :as cc] [klara.compile.emit :as emit]
            [klara.compile.ir :as ir]
            [klara.defs :as d] [klara.world :as w] [klara.stage :as s]
            [klara.eval :as ev] [klara.authority :as a])
  (:import [java.lang.management ManagementFactory] [com.sun.management ThreadMXBean]
           [klara.bench Smc]))

(def sink (volatile! nil))
(def rows (atom []))
(def details (atom {}))
(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
(def ^ThreadMXBean bean (ManagementFactory/getThreadMXBean))
(defn allocated [] (.getThreadAllocatedBytes bean (.threadId (Thread/currentThread))))
(defn sample [f calls]
  (let [b (allocated) t (System/nanoTime)]
    (dotimes [_ calls] (vreset! sink (f)))
    [(/ (double (- (System/nanoTime) t)) calls)
     (/ (double (- (allocated) b)) calls)]))
(defn measure [rq workload mode size f warm batches calls]
  (dotimes [_ warm] (vreset! sink (f)))
  (let [samples (vec (repeatedly batches #(sample f calls)))
        row {:rq rq :workload workload :mode mode :size size
             :ns (median (map first samples)) :bytes (median (map second samples))
             :warmup warm :batches batches :calls calls :samples samples}]
    (swap! rows conj row) row))
(defn equivalent [a b]
  (and (== (double (first a)) (double (first b)))
       (< (Math/abs (- (double (second a)) (double (second b)))) 1e-14)))

(defn kernels [mode]
  (doseq [n [200 2000] [label program] (sort-by key bench/programs)]
    (let [wo (w/make-world) cache (s/make-cache)
          _ (d/define! wo '(def g (fn [x] (* x 2))))
          _ (d/define! wo (list 'def 'f program))
          f (d/lookup (w/snapshot wo) 'f)
          opts (if (= label :calls) {:inline-fuel 0} {})
          exe (when (= mode :compiled) (cc/compile-def wo 'f opts))
          _ (when exe
              (when (= label :calls) (s/install! cache (cc/compile-def wo 'g opts)))
              (s/install! cache exe))
          call (case mode :t0 #(f n) :compiled #(f n)
                     :clojure #((bench/clojure-functions label) n)
                     :java #((bench/java-functions label) n))
          expected (f n)]
      (s/with-cache cache
        (assert (= expected (call)) [mode label n])
        (measure :rq1 label mode n call (if (= mode :t0) 100 10000) 7 (if (= mode :t0) 5 500)))
      (when exe
        (swap! rows conj {:rq :rq1 :workload (keyword (str (name label) "-compile"))
                         :mode mode :size n :ns (* 1e6 (:compile-ms exe)) :bytes 0})
        (swap! details assoc-in [:compile [label n]]
                      (select-keys exe [:compile-ms :allocations-removed :pass-log]))))))

(defn smc-run [mode]
  (let [setup (when (#{:t0 :compiled :dynamic :erased} mode) (smc/setup mode))
        call (case mode :clojure smc/plain :java #(vec (Smc/run)) (:run setup))
        cache (or (:cache setup) (s/make-cache)) expected (smc/plain)]
    (s/with-cache cache
      (assert (equivalent expected (call)) [mode expected (call)])
      (measure (if (#{:dynamic :erased} mode) :rq2 :rq1) :smc mode 384 call 5 7 1)
      (swap! details assoc-in [:smc mode]
             {:result (call) :stats (s/stats cache)
              :compiled-definitions (if (:exe setup) ['emission] [])
              :particle-observations 384 :microsteps 6144
              :checks-erased (get-in setup [:exe :checks-erased])
              :scheduler :t0-continuations :compiled-kernel-calls-per-run (if (:exe setup) 384 0)
              :note "direct entry hits are not included in stage hits" :compile-ms (get-in setup [:exe :compile-ms])}))))

(def affine '(fn [n] (let [o (own [0])]
                      (loop [i 0] (if (< i n)
                                   (do (update! o (fn [v] (assoc v 0 (inc (nth v 0))))) (recur (inc i))) nil))
                      (freeze o))))
(defn authority []
  (doseq [mode [:dynamic :erased] n [0 1000 10000]]
    (let [wo (w/make-world) cache (s/make-cache)
          _ (d/define! wo (list 'def 'counter affine))
          exe (when (= mode :erased) (cc/compile-def wo 'counter))
          _ (when exe (s/install! cache exe))
          f (d/lookup (w/snapshot wo) 'counter)
          call #(binding [a/*store* (a/new-store)] (f n))]
      (s/with-cache cache
        (assert (= [n] (call)))
        (measure :rq2 :affine-loop mode n call (if (= mode :erased) 2000 5) 7 (if (= mode :erased) 100 1)))))
  (smc-run :dynamic) (smc-run :erased))

(defn hot-var [x] (+ x 1))
(defn hot-caller [x] (hot-var x))
(defn redefine-load []
  (doseq [n [10 1000 100000]]
    (let [wo (w/make-world)
          _ (d/define! wo '(def f (fn [x] (+ x 1))))
          _ (d/define! wo '(def g (fn [x] (f x))))
          old (w/fiber wo) cache (s/make-cache)
          _ (s/install! cache (cc/compile-def wo 'g))
          entry (w/entry* (w/snapshot wo) 'g)
          root (reduce (fn [r i] (w/put-entry r (symbol (str "dependent" i)) entry))
                       (w/snapshot wo) (range n))
          _ (reset! (:root wo) root)
          _ (assert (= n (count (disj (w/dependents root 'f) 'g))))
          replacement (w/entry* root 'f)
          publish #(w/publish! wo (fn [r] (w/put-entry r 'f replacement)))
          before (s/stats cache)]
      (measure :rq3 :publish :klara n publish 100 7 100)
      (assert (= before (s/stats cache)))
      (s/with-cache cache
        (dotimes [_ 100] (assert (= 4 (d/eval-in old '(g 3)))))
        (let [events (vec (for [i (range 30)]
                            (let [delta (+ 2 i) t (System/nanoTime)]
                              (d/define! wo (list 'def 'f (list 'fn '[x] (list '+ 'x delta))))
                              (let [published (System/nanoTime) fresh (w/fiber wo)
                                    v (d/eval-in fresh '(g 3)) end (System/nanoTime)]
                                (assert (= (+ 3 delta) v))
                                (assert (= 4 (d/eval-in old '(g 3))))
                                {:publish-ns (- published t) :first-correct-ns (- end published)
                                 :total-ns (- end t)}))))]
          (swap! details assoc-in [:redefinition n] {:events events :stats (s/stats cache)
                                                   :old-new-correct true})
          (swap! rows conj {:rq :rq3 :workload :first-correct :mode :klara :size n
                            :ns (median (map :first-correct-ns events)) :bytes 0
                            :samples events})))))
  (let [events (vec (for [i (range 30)]
                      (let [t (System/nanoTime) delta (+ 2 i)]
                        (alter-var-root #'hot-var (constantly (fn [x] (+ x delta))))
                        (let [published (System/nanoTime) v (hot-caller 3) end (System/nanoTime)]
                          (assert (= (+ 3 delta) v))
                          {:publish-ns (- published t) :first-correct-ns (- end published)}))))]
    (swap! details assoc :clojure-redefinition events)
    (swap! rows conj {:rq :rq3 :workload :first-correct :mode :clojure :size 0
                     :ns (median (map :first-correct-ns events)) :bytes 0 :samples events})))

;; Injection is scoped to experiment-time emission; production compiler is
;; untouched. Every generated checkpoint in this compiler has index zero.
(defn compile-forced [wo]
  (let [original emit/emit-expr]
    (with-redefs [emit/emit-expr
                  (fn patched
                    ([t env tail self] (patched t env tail self false))
                    ([t env tail self consumed]
                     (if (#{:numeric-guard :loop-check} (:op t))
                       `(ev/deopt! 0 [~@(map #(original % env false self) (:live t))])
                       (original t env tail self consumed))))]
      (cc/compile-def wo 'f))))
(def checkpoint-cases
  {:addition '(fn [n probe] (let [seen (count probe) y n] (+ y 1)))
   :vector-alias-closure '(fn [n probe] (let [seen (count probe) v [n 2] alias v
                                           f (fn [x] (+ (first alias) x)) y n]
                                       (+ y (f (second v)))))
   :loop '(fn [n probe] (loop [i 0 acc n] (if (< i 4)
                                        (let [seen (count probe)] (recur (inc i) (+ acc i))) acc)))
   :authority '(fn [n probe] (let [e (evidence 1) paid (spend! e 1/4)
                                  seen (count probe) y n] (+ y (remaining e))))})
(defn observed [f n cache]
  (binding [a/*store* (a/new-store)]
    (let [trace (atom []) probe (reify clojure.lang.Counted
                                 (count [_] (swap! trace conj :count) 1))
          value (try [:value (s/with-cache cache (f n probe))]
                     (catch Exception e [:error (.getName (class e)) (ex-message e)]))]
      {:value value :trace @trace
       :store (mapv #(select-keys % [:kind :status :operation :payload])
                    (vals (:tokens @a/*store*)))})))
(defn deopt []
  (doseq [[label form] checkpoint-cases]
    (let [wo (w/make-world) _ (d/define! wo (list 'def 'f form))
          f (d/lookup (w/snapshot wo) 'f) exe (compile-forced wo)
          _ (assert (= 1 (count (:frame-states exe))) label)
          comparisons (vec (for [n [0 1 1.5 1/2 :bad Long/MAX_VALUE]]
                             (let [cache (doto (s/make-cache) (s/install! exe))
                                   expected (observed f n (s/make-cache)) actual (observed f n cache)]
                               (assert (= expected actual) [label n expected actual])
                               (assert (= 1 (:deopts (s/stats cache))) label)
                               {:input n :observation actual :deopts 1}))) ]
      (swap! details assoc-in [:forced label]
             {:frame-states (:frame-states exe) :comparisons comparisons})))
  (doseq [rate [0 1 10 100]]
    (let [wo (w/make-world)
          _ (d/define! wo '(def f (fn [x] (let [y x] (+ y 1)))))
          f (d/lookup (w/snapshot wo) 'f) exe (cc/compile-def wo 'f)
          inputs (mapv #(if (< (mod % 1000) rate) 1.5 1) (range 1000))
          run (fn []
                (let [cache (doto (s/make-cache) (s/install! exe))]
                  (s/with-cache cache (doseq [x inputs] (assert (= (+ x 1) (f x)))))
                  (s/stats cache)))
          stats (run)]
      (measure :rq4 :mixed-types :feedback rate run 5 7 1)
      (swap! details assoc-in [:mixed rate] {:calls 1000 :nonlong-per-1000 rate :stats stats})) )
  ;; Fresh caches isolate each exit from feedback; recovery includes entry,
  ;; guard, exception transfer and T0 materialization, excludes install.
  (let [wo (w/make-world) _ (d/define! wo '(def f (fn [x] (let [y x] (+ y 1)))))
        f (d/lookup (w/snapshot wo) 'f) exe (cc/compile-def wo 'f)
        times (vec (for [_ (range 100)]
                     (let [cache (doto (s/make-cache) (s/install! exe))]
                       (s/with-cache cache
                         (let [t (System/nanoTime) v (f 1.5) end (System/nanoTime)]
                           (assert (= 2.5 v)) (assert (= 1 (:deopts (s/stats cache))))
                           (- end t))))))]
    (swap! rows conj {:rq :rq4 :workload :recovery :mode :fresh-cache :size 1
                     :ns (median times) :bytes 0 :samples times})
    (swap! details assoc :recovery-ns times)))

(defn naive-counterexample []
  ;; Deliberately broken replay fallback, confined to experiments. An effect
  ;; precedes a guard, then replay from entry performs the same effect again.
  (let [wo (w/make-world)
        _ (d/define! wo '(def f (fn [trace x] (let [seen (count trace) y x] (+ y 1)))))
        f (d/lookup (w/snapshot wo) 'f)
        trace (atom []) probe (reify clojure.lang.Counted (count [_] (swap! trace conj :effect) 1))
        cache (doto (s/make-cache) (s/install! (cc/compile-def wo 'f)))
        correct (s/with-cache cache (f probe 1.5)) correct-trace @trace
        _ (reset! trace [])
        broken-replay (fn [probe x]
                        (count probe)
                        (if (instance? Long x) (+ x 1)
                          (binding [ev/*entry-hook* nil ev/*direct-hook* nil] (f probe x))))
        broken (d/eval-form (w/snapshot wo)
                           (list 'fork ['b (list (list 'quote broken-replay) (list 'quote probe) 1.5)]
                                 '(adopt! b) '(:value b)))]
    (assert (= correct broken 2.5))
    (assert (= [:effect] correct-trace))
    (assert (= [:effect :effect] @trace))
    (swap! details assoc :naive-deopt {:correct correct :broken broken
                                     :correct-trace correct-trace :broken-trace @trace :broken-under-caller-fork true})))

(defn run [mode path]
  (.setThreadAllocatedMemoryEnabled bean true)
  (kernels mode) (smc-run mode)
  (when (= mode :compiled) (authority) (redefine-load) (deopt) (naive-counterexample))
  (let [runtime (ManagementFactory/getRuntimeMXBean)
        result {:mode mode :metadata {:java (System/getProperty "java.runtime.version")
                                     :vm (System/getProperty "java.vm.name") :clojure (clojure-version)
                                     :flags (vec (.getInputArguments runtime))
                                     :pid (.getPid runtime) :processors (.availableProcessors (Runtime/getRuntime))
                                     :max-heap (.maxMemory (Runtime/getRuntime))
                                     :gc (mapv #(.getName %) (ManagementFactory/getGarbageCollectorMXBeans))
                                     :direct-linking (boolean (:direct-linking *compiler-options*))}
                :rows @rows :details @details}]
    (spit (str path ".edn") (pr-str result))
    (spit (str path ".csv")
          (str "rq,workload,mode,size,ns,bytes\n"
               (str/join "\n" (for [r @rows]
                                (str/join "," (map #(if (keyword? %) (name %) (str %))
                                                    ((juxt :rq :workload :mode :size :ns :bytes) r))))) "\n")))
  (shutdown-agents))
