(ns adaptive-affine.calibration-demo
  "Experimental start/await adapter. Policy, classification, learning and
   residual construction are in learned_calibration.klr. No benchmark harness."
  (:require [clojure.java.io :as io]
            [klara.authority :as authority] [klara.code :as code]
            [klara.compile.staged :as staged] [klara.core :as core]
            [klara.defs :as defs] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as world])
  (:import [java.util.concurrent Callable Executors ExecutorService Future TimeUnit]))

(def ^:dynamic *service* nil)

(defn load-world []
  (let [w (world/make-world)]
    (with-open [r (java.io.PushbackReader. (io/reader "experiments/adaptive_affine/learned_calibration.klr"))]
      (doseq [form (take-while #(not= ::eof %) (repeatedly #(read {:eof ::eof} r)))]
        (defs/define! w form)))
    w))

(defn- scalar-term! [source]
  ;; Stronger than simply trusting a Future: finite syntax, no calls, loops,
  ;; world reads or effects. This prototype admits unary +/* Long kernels.
  (when-not (and (code/code? source) (code/closed? source))
    (throw (ex-info "demo requires closed code" {})))
  (let [term (code/s->core (code/code-term source))]
    (when-not (and (= :fn (:op term)) (= 1 (:arity term)) (not (:rest? term)))
      (throw (ex-info "demo requires unary code" {})))
    (doseq [node (tree-seq map? core/children (:body term))]
      (when-not (case (:op node)
                  :quote (instance? Long (:datum node))
                  :local (= 0 (:index node))
                  :prim (and (contains? '#{+ *} (:name node)) (= 2 (count (:args node))))
                  false)
        (throw (ex-info "demo rejects effects and unsupported scalar syntax" {:op (:op node)}))))
    term))

(defn start!
  "Experimental host service: check/compile closed code, then submit it under
   the bound session's exact root. No caller continuation enters the worker."
  [source x root]
  (let [{:keys [basis cache compiled jobs worker]} *service*]
    (when-not (and *service* (identical? basis root) (instance? Long x))
      (throw (ex-info "demo context/input mismatch" {})))
    (let [term (scalar-term! source) id (core/code-id term)
          child (world/fork (world/make-world root))
          ticket (Object.)]
      (let [task (.submit ^ExecutorService worker
                   ^Callable
                   (reify Callable
                     (call [_]
                       (binding [authority/*store* (authority/new-store)
                                 ev/*fiber* nil ev/*outer-k* [] ev/*entry-hook* nil
                                 ev/*direct-hook* nil ev/*context-hook* nil world/*reads* nil]
                         (try
                           ;; Preparation and execution are both off the
                           ;; caller's path. Backend declines are advisory.
                           (when-not (contains? @compiled id)
                             (staged/install! cache root (staged/prepare root source))
                             (swap! compiled conj id))
                           (stage/with-cache cache
                             {:status :ok :value (ev/call-value
                               (ev/run term {:basis (world/snapshot child)}) [x])})
                           ;; A losing branch's arithmetic exception must not
                           ;; escape before the true branch is known.
                           (catch Exception _ {:status :failed}))))))]
        (swap! jobs assoc ticket {:basis root :future task})
        ticket))))

(defn await!
  "Consume one job in the same session and basis; the guest decides whether
   its prediction matches the observation before using the returned value."
  [ticket root]
  (let [{:keys [jobs basis]} *service*
        job (when jobs (get @jobs ticket))]
    (when-not (and job (identical? root basis) (identical? root (:basis job)))
      (throw (ex-info "unknown, consumed or stale demo job" {})))
    (swap! jobs dissoc ticket)
    (.get ^Future (:future job))))

(ev/register-reference-handler! :stage/demo-start
  (fn [[source x] env] (start! source x (:basis env))))
(ev/register-reference-handler! :stage/demo-await
  (fn [[ticket] env] (await! ticket (:basis env))))

(defn session
  "One closeable demo context; no global worker or model. Supply the returned
   model to the next step. Host mutation is scheduling/cache infrastructure."
  []
  (let [w (load-world)]
    {:world w :basis (world/snapshot w) :cache (stage/make-cache)
     :compiled (atom #{}) :jobs (atom {}) :worker (Executors/newSingleThreadExecutor)}))

(defn step! [session model readings x]
  (binding [*service* session authority/*store* (authority/new-store)]
    (ev/call-value (defs/lookup (:basis session) 'predict-and-calibrate) [model readings x])))

(defn close! [{:keys [worker]}]
  (.shutdown ^ExecutorService worker)
  (.awaitTermination ^ExecutorService worker 30 TimeUnit/SECONDS))

(defn example []
  (let [s (session)]
    (try
      (binding [*service* s authority/*store* (authority/new-store)]
        (assoc (ev/call-value (defs/lookup (:basis s) 'calibration-session)
                             [{} [[20 22] [120] [121] [130]] 10])
               :compiled-kernels (count @(:compiled s))))
      (finally (close! s)))))
