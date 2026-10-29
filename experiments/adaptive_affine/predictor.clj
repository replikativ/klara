(ns adaptive-affine.predictor
  "Restricted value speculation diagnostic, not a general effect executor.
   Load bench.clj first. A learned binary abstract outcome suffices because
   this particular continuation factors *exactly* through that outcome."
  (:refer-clojure :exclude [run!])
  (:require [adaptive-affine.bench :as bench]
            [clojure.pprint :as pp]
            [klara.authority :as a]
            [klara.compile.infer-affine :as ia]
            [klara.compile.staged :as staged]
            [klara.defs :as d]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w])
  (:import [java.util.concurrent Callable Executors ExecutorService Future TimeUnit]))

(defn producer
  "Synthetic deterministic CPU work. Only its final parity is relevant to
   the continuation. Deliberately not a realistic abstract interpreter."
  [^long seed ^long work]
  (loop [i (long 0) x seed]
    (if (< i work)
      (recur (inc i) (bit-xor x (bit-and i 1)))
      (if (zero? (bit-and x 1)) :left :right))))

(defn train-one [model site outcome]
  (update-in model [site outcome] (fnil inc 0)))
(defn predict [model site]
  (let [counts (get model site {})]
    (if (>= (get counts :left 0) (get counts :right 0)) :left :right)))
(defn measured [f]
  (let [cpu (bench/cpu) start (System/nanoTime) value (f)]
    {:value value :wall-ns (- (System/nanoTime) start) :cpu-ns (- (bench/cpu) cpu)}))

(defn workload [count wrong-per-ten offset]
  (mapv (fn [i]
          (let [site (mod i 2) wrong? (< (mod (+ i offset) 10) wrong-per-ten)]
            {:site site :seed (long (if wrong? (- 1 site) site))})) (range count)))

(defn context []
  (let [start (System/nanoTime) world (bench/load-world) root (w/snapshot world)
        source (d/lookup root 'counter-code) cache (stage/make-cache)
        candidate (ia/prepare root source)]
    (staged/install! cache root candidate)
    ;; ia/prepare has checked that this exact source has no world reads,
    ;; callbacks, arbitrary host calls, effects or escaping mutable storage.
    {:world world :basis root :cache cache :closure (d/lookup root 'counter)
     :compile-ns (* 1e6 (:compile-ms (staged/prepared-info candidate)))
     :context-setup-ns (- (System/nanoTime) start)}))

(defn follow [ctx outcome n]
  (let [split (if (= outcome :left) (quot n 4) (- n (quot n 4)))]
    (stage/with-cache (:cache ctx) (ev/call-value (:closure ctx) [n split]))))

(defn isolated-follow
  "Only known analyzed follow-up code runs. A future by itself does not
   sandbox arbitrary host mutation. Child publication never touches parent."
  [ctx prediction n]
  (binding [a/*store* (a/new-store)
            ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
            ev/*outer-k* [] ev/*fiber* nil w/*reads* nil]
    (measured
      #(let [child (w/fork (w/make-world (:basis ctx)))
             result (follow ctx prediction n)]
         (d/define! child (list 'def 'speculative-result (list 'quote result)))
         {:basis (:parent child) :prediction prediction
          :root (w/snapshot child) :result result}))))

(defn valid? [ctx actual candidate]
  (and (identical? (:basis ctx) (:basis candidate))
       (= actual (:prediction candidate))))

(defn speculation-step [^ExecutorService worker ctx model {:keys [site seed]} work n]
  (let [start (System/nanoTime) prediction (measured #(predict model site))
        prediction-value (:value prediction)
        ;; Submit before evaluating the true producer. Only an available
        ;; additional core can turn this overlap into a wall-clock gain.
        job (.submit worker ^Callable (reify Callable
                                        (call [_] (isolated-follow ctx prediction-value n))))
        actual (measured #(producer seed work))
        speculative (.get ^Future job)
        validation (measured #(valid? ctx (:value actual) (:value speculative)))
        hit? (:value validation)
        fallback (when-not hit? (measured #(follow ctx (:value actual) n)))
        update (measured #(train-one model site (:value actual)))
        result (if hit? (get-in speculative [:value :result]) (:value fallback))]
    (assert (= result (let [split (if (= :left (:value actual)) (quot n 4) (- n (quot n 4)))]
                       [split (- n split)])))
    (assert (identical? (:basis ctx) (w/snapshot (:world ctx))))
    {:model (:value update) :hit? hit? :value result
     :wall-ns (- (System/nanoTime) start)
     :prediction-ns (:wall-ns prediction) :producer-ns (:wall-ns actual)
     :speculative-ns (:wall-ns speculative) :validation-ns (:wall-ns validation)
     :fallback-ns (or (:wall-ns fallback) 0) :update-ns (:wall-ns update)
     :measured-component-cpu-ns (reduce + (map #(or (:cpu-ns %) 0)
                                              [prediction actual speculative validation fallback update]))
     :wasted-worker-cpu-ns (if hit? 0 (:cpu-ns speculative))}))

(defn scenario [worker ctx {:keys [name work n wrong-per-ten] :as configuration}]
  (let [training (workload 24 1 3)
        trained (measured #(reduce (fn [model {:keys [site seed]}]
                                    (train-one model site (producer seed work))) {} training))
        requests (workload 40 wrong-per-ten 0)
        baseline (mapv (fn [{:keys [seed]}]
                         (measured #(follow ctx (producer seed work) n))) requests)
        steps (loop [model (:value trained) xs requests results []]
                (if-let [request (first xs)]
                  (let [result (speculation-step worker ctx model request work n)]
                    (recur (:model result) (next xs) (conj results (dissoc result :model)))) results))
        _ (assert (= (mapv :value baseline) (mapv :value steps)))
        accuracy (/ (count (filter :hit? steps)) (double (count steps)))
        baseline-ns (reduce + (map :wall-ns baseline))
        speculation-ns (reduce + (map :wall-ns steps))
        saving (/ (- baseline-ns speculation-ns) (double (count steps)))
        setup (+ (:wall-ns trained) (:worker-initialization-ns ctx 0))]
    {:configuration configuration :training (dissoc trained :value)
     :initial-model (:value trained) :accuracy accuracy
     :baseline-wall-ns baseline-ns :speculation-wall-ns speculation-ns
     :baseline-measured-cpu-ns (reduce + (map :cpu-ns baseline))
     :speculation-measured-component-cpu-ns (reduce + (map :measured-component-cpu-ns steps))
     :wasted-worker-cpu-ns (reduce + (map :wasted-worker-cpu-ns steps))
     :observed-saving-ns-per-request saving
     :diagnostic-break-even-requests (when (pos? saving) (long (Math/ceil (/ setup saving))))
     :with-context-setup-break-even-requests
     (when (pos? saving) (long (Math/ceil (/ (+ setup (:context-setup-ns ctx)) saving))))
     :samples steps :baseline-samples baseline}))

(defn run!
  ([] (run! "experiments/adaptive_affine/predictor-s28-results.edn"))
  ([output]
  (let [ctx (context) worker-start (System/nanoTime) worker (Executors/newSingleThreadExecutor)]
    (try
      ;; Warm both producer and actual child workflow before the measurements.
      (dotimes [_ 40]
        (producer 1 1000000)
        (.get ^Future (.submit worker ^Callable
                               (reify Callable (call [_] (isolated-follow ctx :left 10000))))))
      (let [ctx (assoc ctx :worker-initialization-ns (- (System/nanoTime) worker-start))
            configurations [{:name :small-high-accuracy :work 1000 :n 256 :wrong-per-ten 1}
                            {:name :large-high-accuracy :work 8000000 :n 200000 :wrong-per-ten 1}
                            {:name :large-distribution-shift :work 8000000 :n 200000 :wrong-per-ten 5}]
            results (mapv #(scenario worker ctx %) configurations)
            ;; The large case was close enough to zero to change sign during
            ;; development. Retain additional samples instead of choosing a win.
            repeats (mapv (fn [_] (scenario worker ctx (second configurations))) (range 2))
            report {:java (System/getProperty "java.runtime.version") :compile-ns (:compile-ns ctx)
                    :context-setup-ns (:context-setup-ns ctx)
                    :worker-initialization-including-warmup-ns (:worker-initialization-ns ctx)
                    :results results :large-high-accuracy-repeats repeats
                    :limitations [:synthetic-outcomes :one-process :fixed-order :extra-worker-core
                                  :not-an-abstract-interpreter :not-general-speculative-effects
                                  :cpu-excludes-runtime-thread-pool-and-gc-overhead
                                  :no-retained-memory-accounting :nonstationary-break-even-estimate]}]
        (spit output (with-out-str (pp/pprint report)))
        (pp/pprint (reduce (fn [r key]
                            (update r key #(mapv (fn [row] (dissoc row :samples :baseline-samples)) %)))
                          report [:results :large-high-accuracy-repeats]))
        report)
      (finally (.shutdown worker) (.awaitTermination worker 30 TimeUnit/SECONDS))))))
