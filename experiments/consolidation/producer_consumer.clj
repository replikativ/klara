(ns consolidation.producer-consumer
  "Known pure producers export checked immutable value facts. Unary consumers
   discharge input guards with those facts; pure batches admit once. Drivers
   and core/model/JVM correspondence are trusted/tested implementation bridges."
  (:require [consolidation.interval :as interval]
            [consolidation.producer-model :as model]
            [klara.code :as code] [klara.core :as c] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as w]))

(def bootstrap @model/proof-state)
(deftype Producer [source max-x upper function roots witness])
(defmethod print-method Producer [_ out] (.write ^java.io.Writer out "#<bounded-producer>"))
(defn- fail [why] (throw (ex-info (name why) {:reason why})))

(def ^:private reference-roots
  (into #{[:host-root 'klara.core/prims c/prims]}
        (for [op '[+ *]] [:host-root (symbol "clojure.core" (name op)) @(ns-resolve 'clojure.core op)])))

(defn prepare-producer [source max-x]
  (when-not (every? #(stage/guard-holds? % {}) reference-roots) (fail :producer-host-root))
  (when-not (and (code/code? source) (code/closed? source)) (fail :producer-scope))
  (let [term (code/s->core (code/code-term source))]
    (when-not (and (= :fn (:op term)) (= 1 (:arity term)) (not (:rest? term))) (fail :producer-interface))
    (let [bounds (interval/certify (:body term) max-x Long/MAX_VALUE)
          witness (model/witness bounds max-x) x (with-meta (gensym "x") {:tag 'long})
          emit (fn emit [t]
                 (case (:op t)
                   :local (if (zero? (:index t)) x (fail :producer-scope))
                   :quote (:datum t)
                   :prim (list* (symbol "clojure.core" (name (:name t))) (map emit (:args t)))
                   (fail :producer-operation)))
          form (list 'fn (with-meta [x] {:tag 'long}) (emit (:body term)))
          f (binding [*unchecked-math* false *ns* (the-ns 'consolidation.producer-consumer)] (eval form))
          _ (when-not (instance? clojure.lang.IFn$LL f) (fail :producer-primitive-ABI))
          ]
      (Producer. source max-x (long (:upper bounds)) f reference-roots
                 (assoc witness :source-id (c/code-id term) :bound-proof bounds)))))

(defn producer-info [^Producer p]
  {:source-id (get (.-witness p) :source-id) :input-max (.-max-x p) :output-max (.-upper p)
   :witness (select-keys (.-witness p) [:goal-sha256 :proof-sha256])})

(defn produce [^Producer producer input]
  (let [value (stage/evidence-value input)]
    (when-not (stage/evidence-holds? input [:bounded-nat-vector Long/MAX_VALUE (.-max-x producer)] value)
      (fail :producer-input-facts))
    (when-not (every? #(stage/guard-holds? % {}) (.-roots producer)) (fail :producer-host-root))
    (let [^clojure.lang.PersistentVector v value n (.count v)
          ^clojure.lang.IFn$LL f (.-function producer)
          result (loop [i (long 0) out (.asTransient v)]
                   ;; Each original element is read from v; no mutation of v.
                   (if (< i n)
                     (recur (inc i) (.assocN ^clojure.lang.ITransientVector out (int i)
                                             (Long/valueOf (.invokePrim f (long (.nth v (int i)))))))
                     (.persistent ^clojure.lang.ITransientVector out)))]
      (stage/produced-vector-evidence result (.-upper producer)
                                      {:producer-id (get (.-witness producer) :source-id)
                                       :proof-sha256 (get (.-witness producer) :proof-sha256)}))))

(deftype Consumer [closure site])
(defmethod print-method Consumer [_ out] (.write ^java.io.Writer out "#<evidence-consumer>"))
(defn consumer [cache f]
  (when-not (ev/closure? f) (fail :consumer-interface))
  (Consumer. f (stage/make-evidence-site cache f)))
(defn- context-root [^Consumer consumer basis]
  (or (ev/closure-basis (.-closure consumer)) basis))
(defn- fallback [^Consumer consumer evidence basis kont]
  (when (some #(= :handle (:tag %)) kont) (fail :fallback-requires-Klara-context))
  (binding [ev/*basis* basis ev/*outer-k* (list kont)
            ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
    (ev/call-value (.-closure consumer) [(stage/evidence-value evidence)])))
(defn consume [^Consumer consumer evidence basis kont]
  (let [root (context-root consumer basis)]
    (if-let [exe ((.-site consumer) evidence root kont)]
      ((:invoke1 exe) (stage/evidence-value evidence))
      (fallback consumer evidence root kont))))

(defn- run-batch [f value ^long repetitions]
  (if (instance? clojure.lang.IFn$OL f)
    (loop [i (long 0) result (long 0)]
      (if (< i repetitions)
        (recur (inc i) (.invokePrim ^clojure.lang.IFn$OL f value)) result))
    (loop [i (long 0) result nil]
      (if (< i repetitions) (recur (inc i) (f value)) result))))

(defn consume-batch
  "A known pure driver: no user callback or source effects between admission
   and fixed-arity calls. Returns the last result; zero iterations inspect no input."
  [^Consumer consumer evidence repetitions basis kont]
  (when-not (and (instance? Long repetitions) (<= 0 repetitions)) (fail :batch-count))
  (when (pos? repetitions)
    (let [root (context-root consumer basis)]
      (if-let [exe ((.-site consumer) evidence root kont)]
        (run-batch (:invoke1 exe) (stage/evidence-value evidence) repetitions)
        (loop [i (long 0) result nil]
          (if (< i repetitions)
            (recur (inc i) (fallback consumer evidence root kont)) result))))))

(defn attempt
  "Return a value or a T0 call plan. The guest wrapper executes fallback in
   its original CEK continuation; a host callback must not restart that call."
  [^Consumer consumer evidence n basis kont]
  (when-not (and (instance? Long n) (<= 0 n)) (fail :batch-count))
  (if (zero? n) {:status :completed :value nil}
    (let [root (context-root consumer basis)]
      (if-let [exe ((.-site consumer) evidence root kont)]
        {:status :completed
         :value (run-batch (:invoke1 exe) (stage/evidence-value evidence) n)}
        {:status :fallback :function (.-closure consumer)
         :input (stage/evidence-value evidence) :repetitions n}))))

(ev/register-reference-handler! :stage/refine-input
 (fn [[predicate value] _] (or (stage/refine-argument predicate value) {:status :declined :reason :input-domain})))
(ev/register-reference-handler! :stage/prepare-producer (fn [[source max-x] _] (prepare-producer source max-x)))
(ev/register-reference-handler! :stage/produce (fn [[producer evidence] _] (produce producer evidence)))
(ev/register-reference-handler! :stage/input-value (fn [[evidence] _] (stage/evidence-value evidence)))
(ev/register-reference-handler! :stage/consumer
 (fn [[f] _] (consumer stage/*cache* f)))
(ev/register-reference-handler! :stage/try-consume
 (fn [[consumer evidence] env] (attempt consumer evidence 1 (:basis env) (mapcat identity ev/*outer-k*))))
(ev/register-reference-handler! :stage/try-consume-batch
 (fn [[consumer evidence n] env] (attempt consumer evidence n (:basis env) (mapcat identity ev/*outer-k*))))
