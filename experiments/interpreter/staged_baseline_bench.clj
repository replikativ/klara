(ns interpreter.staged-baseline-bench
  "Matched diagnostic, not a general baseline promotion benchmark.")

(def namespace-start (System/nanoTime))
(require '[klara.compile.core :as compiler] '[klara.compile.budget :as budget]
         '[klara.compile.guest :as guest] '[klara.core :as core]
         '[klara.defs :as defs] '[klara.eval :as ev] '[klara.expand :as expand]
         '[klara.stage :as stage] '[klara.world :as world])
(def namespace-ms (/ (- (System/nanoTime) namespace-start) 1e6))

(def cases
  [{:name :tiny :source '(fn [x] (+ x 1)) :arguments [3]}
   {:name :branchy :source '(fn [x] (let [y (+ x 1)] (if (< y 0) (- y) (* y y)))) :arguments [-3]}
   {:name :recurrence :source '(fn [n] (loop [i n a [1] b [2]]
                                       (if (> i 0) (recur (dec i) b (conj a i)) a))) :arguments [64]}
   {:name :guest-transfer :source guest/transfer-source
    :arguments [['a 'b 'c] [{:op :local :name 'c} {:op :local :name 'a} {:op :local :name 'b}]]}
   {:name :acyclic :source '(fn [x] (+ (helper x) (helper x))) :arguments [4]}
   {:name :unsupported :source '(fn [x] (code (+ (esc x) 1))) :arguments []}])

(defn sample [f n]
  (let [start (System/nanoTime)]
    (dotimes [_ n] (f))
    (/ (- (System/nanoTime) start) (double n))))

(defn measure [{:keys [name source arguments]}]
  (let [w (world/make-world)
        _ (defs/define! w '(def helper (fn [x] (+ (* x x) 1))))
        _ (defs/define! w (list 'def 'subject source))
        root (world/snapshot w) b (budget/budget)
        start (System/nanoTime)
        candidate (try (compiler/compile-def root 'subject {:mode :baseline :budget b})
                       (catch Exception e {:declined (or (:reason (ex-data e)) (.getName (class e)))}))
        preparation-ms (/ (- (System/nanoTime) start) 1e6)
        provenance {:case name :source-id (core/code-id (ev/closure-term (:value (world/entry* root 'subject))))
                    :preparation-ms preparation-ms :usage (budget/usage b)}]
    (if (:declined candidate)
      (assoc provenance :status :declined :reason (:declined candidate))
      (let [cache (stage/make-cache) reference (stage/make-cache)
            install-start (System/nanoTime)
            _ (doseq [dependency (:dependencies candidate)] (stage/install! cache dependency))
            _ (stage/install! cache candidate)
            install-ms (/ (- (System/nanoTime) install-start) 1e6)
            term (expand/expand-expr (list* 'subject (map #(list 'quote %) arguments)) root)
            run #(stage/with-cache % (ev/run term {:basis root}))
            t0 #(run reference) compiled #(run cache)
            expected (t0)
            _ (assert (= expected (compiled)))
            cold-start (System/nanoTime) _ (compiled)
            cold-call-ns (- (System/nanoTime) cold-start)]
        (dotimes [_ 200] (t0) (compiled))
        (let [samples (mapv (fn [i]
                              ;; Alternate order to limit a fixed warmup bias.
                              (if (even? i)
                                {:t0-ns (sample t0 100) :baseline-ns (sample compiled 100)}
                                (let [native (sample compiled 100)]
                                  {:t0-ns (sample t0 100) :baseline-ns native}))) (range 7))]
          (assoc provenance :status :installed :validation-install-ms install-ms
                 :early-call-ns cold-call-ns :samples samples
                 :transfers (mapv #(select-keys % [:producer :producer-code-id]) (:transfer-receipts candidate))
                 :cache (stage/stats cache)))))))

(defn -main [& _]
  (prn {:java-version (System/getProperty "java.version")
        :java-vm (System/getProperty "java.vm.name") :java-vendor (System/getProperty "java.vendor")
        :compiler-namespace-load-ms namespace-ms :warmup-calls 200 :calls-per-sample 100
        :results (mapv measure cases)}))
