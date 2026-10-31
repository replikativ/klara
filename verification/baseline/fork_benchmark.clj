(ns baseline.fork-benchmark
  "Replayable pure subset experiment. Semantic admission precedes timing;
   application forks share JVM JIT/GC/clock state. No automatic promotion."
  (:require [clojure.java.io :as io] [clojure.pprint :as pp]
            [klara.compile.budget :as budget] [klara.compile.funding :as funding]
            [klara.compile.service :as service] [klara.compile.subject :as subject]
            [klara.compile.staged :as staged] [klara.core :as core] [klara.defs :as defs]
            [klara.eval :as ev] [klara.stage :as stage] [klara.world :as world]
            [klara.authority :as authority]))

(def source '(fn [n] (loop [i 0 total 0]
                      (if (< i n) (recur (inc i) (+ total i)) total))))

(defn eligible!
  "Pure source/dependency and exact inert-input admission, plus a fuel-bounded
   successful reference run for this input. This is not a general persistence
   or termination proof, nor approval of arbitrary candidate implementations."
  [b root symbol arguments]
  (service/data! b arguments)
  (service/invoke b root symbol arguments 16384))

(defn- elapsed [f]
  (let [start (System/nanoTime) value (f)] {:value value :ns (- (System/nanoTime) start)}))
(defn- median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))

(defn run-study! [label]
  (let [w (world/make-world) _ (defs/define! w (list 'def 'kernel source))
        root (world/snapshot w) f (defs/lookup root 'kernel) args [100]
        job (funding/create {}) b (funding/counter job)
        eligibility (elapsed #(eligible! b root 'kernel args)) witness (:value eligibility)
        code (defs/eval-form root (list 'code source))
        compilation (elapsed #(staged/request root (subject/closed root code)
                                             {:job job :backend :baseline}))
        request (:value compilation)
        _ (assert (= :prepared (:status request)))
        candidate (:candidate request) cache (stage/make-cache)
        installation (elapsed #(staged/install! cache root (staged/prevalidate candidate)))
        execute (fn [optimized?]
                  (let [replica (world/fork w) basis (world/snapshot replica)]
                    (binding [authority/*store* (authority/new-store) ev/*basis* basis ev/*mint* basis
                              ev/*fiber* (world/fiber replica) ev/*outer-k* []]
                      (let [r (if optimized?
                                (stage/with-cache cache (elapsed #(ev/call-value f args)))
                                (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
                                  (elapsed #(ev/call-value f args))))]
                        (assert (identical? basis (world/snapshot replica))) r))))
        pair (fn [i]
               ;; Reserve reference-transition-equivalent work for both runs;
               ;; this is sponsorship accounting, not a native instruction count.
               (budget/charge! b :work (* 2 (:transitions witness)))
               (let [order (if (even? i) [:reference :candidate] [:candidate :reference])
                     r (into {} (for [k order] [k (execute (= k :candidate))]))]
                 (assert (= (:value witness) (get-in r [:reference :value]) (get-in r [:candidate :value]))) r))
        _ (dotimes [i 5] (pair i)) samples (mapv pair (range 7))
        stats (stage/stats cache)
        _ (assert (and (pos? (:hits stats)) (zero? (:fallbacks stats))))
        _ (assert (identical? root (world/snapshot w)))
        report {:label label :source source :arguments args :source-id (core/code-id (:generic (.-executable ^klara.compile.staged.Prepared candidate)))
                :reference-transitions (:transitions witness) :reference-value (:value witness)
                :eligibility-ns (:ns eligibility) :preparation-ns (:ns compilation)
                :validation-installation-ns (:ns installation)
                :samples samples :median-ns (into {} (for [k [:reference :candidate]]
                                                      [k (median (map #(get-in % [k :ns]) samples))]))
                :usage (funding/usage job) :stats stats
                :java (System/getProperty "java.runtime.version")
                :promotion :not-performed
                :limits [:pure-source-subset :one-terminating-input :trusted-tested-baseline-bridge
                         :guard-costs-included :one-warm-process :shared-host-jit-gc-clock
                         :timings-are-profitability-evidence-not-semantic-proof
                         :no-general-stateful-replay-or-native-preemption]
                :source-sha256 (into {} (for [path (concat ["verification/baseline/fork_benchmark.clj"]
                                                         (map str (filter #(.isFile %) (file-seq (io/file "src")))))]
                                        [path (core/sha256 (slurp path))]))}
        path (str "target/fork-benchmark/" label ".edn")]
    (io/make-parents path) (spit path (with-out-str (pp/pprint report)))
    (select-keys report [:label :reference-transitions :median-ns :usage :promotion])))

(defn -main [& [label]] (prn (run-study! (or label "fresh"))))
