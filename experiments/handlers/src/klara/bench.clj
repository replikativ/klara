(ns klara.bench
  "Benchmark registry and harness. One benchmark per JVM:
     java ... clojure.main -m klara.bench <id>
  prints one EDN map on stdout."
  (:require [klara.fx :as fx]
            [klara.cps :as c]
            [klara.loom :as l]
            [klara.hmm :as h]
            [klara.work :as w :refer [tick unused stop u0 u1 u2 u3 u4 u5 u6 u7 u8 u9]])
  (:import [klara.work IBox]))

(set! *warn-on-reflection* true)
(set! *unchecked-math* true)

(def ^:const N 10000000)   ; workload (i): 10^7 performs
(def ^:const M 1000000)    ; per-iteration frame / abort benchmarks
(def ^:const P 1000)       ; particles

;; ---------------------------------------------------------------------------
;; (i) counter loops

(defn loop-direct [^IBox b]
  (loop [i 0] (if (< i N) (do (w/add-fn b 1) (recur (inc i))) (.get b))))

(defn loop-protocol [b]
  (loop [i 0] (if (< i N) (do (w/padd b 1) (recur (inc i))) (.get ^IBox b))))

(defn loop-fast [^IBox b]
  (loop [i 0] (if (< i N) (do (fx/perform tick 1) (recur (inc i))) (.get b))))

(defn loop-g [^IBox b]
  (loop [i 0] (if (< i N) (do (fx/perform-g tick 1) (recur (inc i))) (.get b))))

(defn loop-sv [^IBox b]
  (loop [i 0] (if (< i N) (do (fx/perform-sv tick 1) (recur (inc i))) (.get b))))

(defn loop-dyn [^IBox b]
  (loop [i 0] (if (< i N) (do (fx/perform-dyn :tick 1) (recur (inc i))) (.get b))))

(defn loop-list [^IBox b]
  (loop [i 0] (if (< i N) (do (fx/perform-l tick 1) (recur (inc i))) (.get b))))

(def cps-counter
  (c/cps (loop [i 0] (if (< i N) (do (c/perform tick 1) (recur (inc i))) :done))))

(defn loop-loom [^IBox b ^long n]
  (loop [i 0] (if (< i n) (do (l/perform tick 1) (recur (inc i))) (.get b))))

(defmacro with-10-unused-fast [& body]
  `(fx/handle [u0 identity u1 identity u2 identity u3 identity u4 identity
               u5 identity u6 identity u7 identity u8 identity u9 identity]
     ~@body))

(defmacro with-10-unused-list [& body]
  (reduce (fn [acc op] `(fx/handle-l [~op identity] ~acc))
          `(do ~@body) '[u0 u1 u2 u3 u4 u5 u6 u7 u8 u9]))

;; three clause classes doing identical work, for the megamorphic variant
(defn clause-a [^IBox b] (fn [x] (.add b x)))
(defn clause-b [^IBox b] (fn [x] (.add b x)))
(defn clause-c [^IBox b] (fn [x] (.add b x)))
(def ^"[J" rot (long-array 1))

;; ---------------------------------------------------------------------------
;; (iii) unused frames

(defn u-outer-fast [^IBox b]
  (fx/handle [unused identity] (loop-direct b)))

(defn u-iter-fast [^IBox b]
  (loop [i 0] (if (< i M) (do (fx/handle [unused identity] (w/add-fn b 1)) (recur (inc i))) (.get b))))

(defn u-iter-abort [^IBox b]
  (loop [i 0] (if (< i M) (do (fx/handle-abort stop identity (w/add-fn b 1)) (recur (inc i))) (.get b))))

(defn u-iter-dyn [^IBox b]
  (loop [i 0] (if (< i M) (do (fx/handle-dyn [:unused identity] (w/add-fn b 1)) (recur (inc i))) (.get b))))

(defn u-iter-sv [^IBox b]
  (loop [i 0] (if (< i M) (do (fx/handle-sv [unused identity] (w/add-fn b 1)) (recur (inc i))) (.get b))))

(defn u-iter-cps [^IBox b]
  (loop [i 0] (if (< i M) (do (c/handle [unused (fn [x k] (k x))] (c/run (c/cps (w/add-fn b 1)))) (recur (inc i))) (.get b))))

(defn u-iter-loom [^IBox b]
  (loop [i 0] (if (< i M) (do (l/handle [unused identity] (w/add-fn b 1)) (recur (inc i))) (.get b))))

(defn u-iter-none [^IBox b]
  (loop [i 0] (if (< i M) (do (w/add-fn b 1) (recur (inc i))) (.get b))))

;; a perform that is reachable but never executed
(defn u-maybe-fast [^IBox b]
  (loop [i 0] (if (< i N) (do (when (neg? i) (fx/perform unused 0)) (w/add-fn b 1) (recur (inc i))) (.get b))))

(defn u-maybe-cps [b]
  (c/cps (loop [i 0] (if (< i N) (do (when (neg? i) (c/perform unused 0)) (w/add-fn b 1) (recur (inc i))) :done))))

;; ---------------------------------------------------------------------------
;; (3) abort

(defn deep-abort ^long [^long n b]
  (if (zero? n) (do (w/add-fn b 1) (fx/perform-abort stop 1)) (inc (deep-abort (dec n) b))))
(defn deep-ret ^long [^long n b]
  (if (zero? n) (long (w/add-fn b 1)) (inc (deep-ret (dec n) b))))
(defn deep-exinfo ^long [^long n b]
  (if (zero? n) (do (w/add-fn b 1) (fx/throw-exinfo 1)) (inc (deep-exinfo (dec n) b))))

(defn a-local [^IBox b]
  (loop [i 0] (if (< i M) (do (fx/handle-abort stop identity (do (w/add-fn b 1) (fx/perform-abort stop 1))) (recur (inc i))) (.get b))))
(defn a-d10 [^IBox b]
  (loop [i 0] (if (< i M) (do (fx/handle-abort stop identity (deep-abort 10 b)) (recur (inc i))) (.get b))))
(defn a-ret-d10 [^IBox b]
  (loop [i 0] (if (< i M) (do (deep-ret 10 b) (recur (inc i))) (.get b))))
(defn a-exinfo-d10 [^IBox b]
  (loop [i 0] (if (< i M) (do (fx/handle-abort-exinfo identity (deep-exinfo 10 b)) (recur (inc i))) (.get b))))

;; ---------------------------------------------------------------------------
;; registry: id -> {:ops performs (or iterations) per call, :unit, :f}

(def benches
  (let [b (w/box)]
    {;; (i) counter
     :i/direct-fn   {:ops N :f #(loop-direct b)}
     :i/protocol    {:ops N :f #(loop-protocol b)}
     :i/fast-tl     {:ops N :f #(fx/handle [tick (fn [x] (.add b x))] (loop-fast b))}
     :i/fast-tl-mega {:ops N :f #(let [r (mod (aset rot 0 (inc (aget rot 0))) 3)
                                       cl (case (int r) 0 (clause-a b) 1 (clause-b b) (clause-c b))]
                                   (fx/handle [tick cl] (loop-fast b)))}
     :i/fast-tl-depth10 {:ops N :f #(fx/handle [tick (fn [x] (.add b x))] (with-10-unused-fast (loop-fast b)))}
     :i/fast-global {:ops N :f #(fx/handle-g [tick (fn [x] (.add b x))] (loop-g b))}
     :i/fast-sv     {:ops N :f #(fx/handle-sv [tick (fn [x] (.add b x))] (loop-sv b))}
     :i/fast-dyn    {:ops N :f #(fx/handle-dyn [:tick (fn [x] (.add b x))] (loop-dyn b))}
     :i/list-depth0 {:ops N :f #(fx/handle-l [tick (fn [x] (.add b x))] (loop-list b))}
     :i/list-depth10 {:ops N :f #(fx/handle-l [tick (fn [x] (.add b x))] (with-10-unused-list (loop-list b)))}
     :i/cps         {:ops N :f #(c/handle [tick (fn [x k] (k (.add b x)))] (c/run cps-counter))}
     :i/loom        {:ops M :f #(l/handle [tick (fn [x] (.add b x))] (loop-loom b M))}
     ;; (iii) unused frames
     :iii/none-1e7       {:ops N :f #(loop-direct b)}
     :iii/fast-outer     {:ops N :f #(u-outer-fast b)}
     :iii/maybe-fast     {:ops N :f #(u-maybe-fast b)}
     :iii/maybe-cps      {:ops N :f #(c/handle [unused (fn [x k] (k x))] (c/run (u-maybe-cps b)))}
     :iii/none-iter      {:ops M :f #(u-iter-none b)}
     :iii/fast-iter      {:ops M :f #(u-iter-fast b)}
     :iii/abort-iter     {:ops M :f #(u-iter-abort b)}
     :iii/dyn-iter       {:ops M :f #(u-iter-dyn b)}
     :iii/sv-iter        {:ops M :f #(u-iter-sv b)}
     :iii/cps-iter       {:ops M :f #(u-iter-cps b)}
     :iii/loom-iter      {:ops M :f #(u-iter-loom b)}
     ;; (3) abort
     :abort/local        {:ops M :f #(a-local b)}
     :abort/ret-d10      {:ops M :f #(a-ret-d10 b)}
     :abort/stackless-d10 {:ops M :f #(a-d10 b)}
     :abort/exinfo-d10   {:ops M :f #(a-exinfo-d10 b)}
     ;; (ii) HMM: ops = program executions (particles or enumerated paths)
     :ii/is-direct  {:ops P :f #(h/is-direct P 42)}
     :ii/is-fast    {:ops P :f #(h/is-fast P 42)}
     :ii/is-cps     {:ops P :f #(h/is-cps P 42)}
     :ii/is-loom    {:ops P :f #(h/is-loom P 42)}
     :ii/smc-cps    {:ops P :f #(h/smc-cps P 42)}
     :ii/smc-replay {:ops P :f #(h/smc-replay P 42)}
     :ii/enum-direct {:ops (bit-shift-left 1 h/T) :f h/enum-direct}
     :ii/enum-cps    {:ops (bit-shift-left 1 h/T) :f h/enum-cps}
     :ii/enum-replay {:ops (bit-shift-left 1 h/T) :f h/enum-replay}}))

;; ---------------------------------------------------------------------------
;; harness

(def sink (volatile! nil))

(defn- quantile [xs q]
  (let [v (vec (sort xs)) n (count v)]
    (nth v (min (dec n) (int (Math/floor (* q n)))))))

(defn measure
  [f ops {:keys [warmup-ms samples min-sample-ms]
          :or {warmup-ms 3000 samples 15 min-sample-ms 200}}]
  (let [t0 (System/nanoTime)
        warm-calls (loop [k 0]
                     (vreset! sink (f))
                     (if (or (< k 5) (< (- (System/nanoTime) t0) (* warmup-ms 1000000)))
                       (recur (inc k)) (inc k)))
        per-call (/ (double (- (System/nanoTime) t0)) warm-calls)
        reps (max 1 (long (Math/ceil (/ (* min-sample-ms 1e6) per-call))))
        xs (vec (for [_ (range samples)]
                  (let [t (System/nanoTime)]
                    (dotimes [_ reps] (vreset! sink (f)))
                    (/ (double (- (System/nanoTime) t)) reps ops))))]
    {:median (quantile xs 0.5) :min (apply min xs)
     :p25 (quantile xs 0.25) :p75 (quantile xs 0.75)
     :reps reps :warm-calls warm-calls :samples xs}))

(defn -main [& [id & opts]]
  (let [k (keyword id)
        {:keys [ops f]} (or (get benches k) (throw (ex-info "no such bench" {:id id})))
        r (measure f ops (if (seq opts) (read-string (first opts)) {}))]
    (prn (merge {:id k :ops ops
                 :java (System/getProperty "java.vm.version")
                 :vm (System/getProperty "java.vm.name")
                 :result (pr-str @sink)}
                (dissoc r :samples)
                {:samples (mapv #(/ (Math/round (* 1000.0 (double %))) 1000.0) (:samples r))}))
    (shutdown-agents)
    (System/exit 0)))
