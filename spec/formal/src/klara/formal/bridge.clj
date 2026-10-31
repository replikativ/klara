(ns klara.formal.bridge
  "The trusted bridge between the implementation and the formal semantics
  (spec/formal/README.md#the-bridge).

  `quote-term` maps a nucleus Core term (as produced by the real reader and
  expander) to the formal `Tm`, or throws ::outside when the term is not in
  the formalized fragment. `run-model` iterates the kernel-checked `step`.
  `compare-source` evaluates a program form by form in both the CEK machine
  and the model, and compares observations.

  This file is small on purpose: it is what the differential tests and the
  reflection proofs (L4) trust."
  (:require [klara.formal.core :as f]
            [klara.host.api :as k]
            [klara.lang.term :as t]
            [klara.lang.expand :as ex]
            [klara.runtime.session :as session]
            [klara.runtime.value :as v])
  (:import [klara.runtime.value Closure Code]))

;; ---------------------------------------------------------------------------
;; Runtime representation of the formal inductives (ansatz codegen):
;; tagged vectors [ctor-index field ...]; World/Worlds/Option use nil for
;; their nullary constructor; List is a Clojure list.

(def tag
  {:var 0 :lit 1 :lam 2 :app 3 :let 4 :if 5 :letrec 6 :fix 7 :glob 8 :pin 9 :prim 10
   :perform 11 :handle 12 :handling 13 :code 14 :esc 15 :run 16 :gvar 17
   :nlam 18 :nlet 19 :nletrec 20 :nfix 21 :nhandle 22})

(def tag-name (zipmap (vals tag) (keys tag)))

(def prim-op
  "Enum constructors: ansatz represents index 0 as nil, the others by index."
  {:add nil :sub 1 :mul 2 :eq 3 :lt 4})

(defn- tm [k & fields] (into [(tag k)] fields))

(defn outside [why & {:as data}]
  (throw (ex-info (str "outside the formal fragment: " why) (merge {::outside why} data))))

(defn outside? [e] (and (instance? clojure.lang.ExceptionInfo e) (::outside (ex-data e))))

(defn- intern! [table x]
  (or (get @table x) (let [i (count @table)] (swap! table assoc x i) i)))

(defn- datum [ctx x]
  (cond (nil? x) [0]
        (boolean? x) [1 x]
        (and (integer? x) (<= Long/MIN_VALUE x Long/MAX_VALUE)) [2 (long x)]
        (keyword? x) [3 (intern! (:kws ctx) x)]
        :else (outside "constant" :value x)))

;; ---------------------------------------------------------------------------
;; Quoting

(declare quote*)

(defn- inline-holes
  "The template of a :code term with each of its holes replaced by an esc of
   the hole's term (holes of nested code terms are left to them)."
  [u id holes]
  (if (and (= :hole (:op u)) (= id (:code u)))
    {:op :app :fn {:op :host :name ::esc} :args [(nth holes (:index u))]}
    (t/with-children u (map #(inline-holes % id holes) (t/children u)))))

(defn- index-of [env n]
  (let [i (.lastIndexOf ^java.util.List env n)]
    (when (neg? i) (outside "free local" :local n))
    (- (count env) 1 i)))

(defn- lams [ctx env params body]
  (if (empty? params)
    (quote* ctx env body)
    (tm :lam (lams ctx (conj env (first params)) (rest params) body))))

(defn- self-recursive? [self body]
  (and self (or (contains? (t/free-locals body) self)
                (some #(and (= :recur (:op %)) (= self (:target %))) (t/nodes body)))))

(defn- quote-fn
  "(fn [x y] b) curried; a self-referencing fn is fix (index 1 = itself)."
  [ctx env {:keys [self arities]}]
  (when (not= 1 (count arities)) (outside "multi-arity fn"))
  (let [{:keys [params rest body]} (first arities)
        params (if (empty? params) ['_unit] params)]
    (when rest (outside "variadic fn"))
    (if (self-recursive? self body)
      (tm :fix (lams ctx (conj env self (first params)) (next params) body))
      (lams ctx env params body))))

(defn- curry [ctx env f args]
  (reduce (fn [acc a] (tm :app acc (quote* ctx env a)))
          f (if (empty? args) [(t/const nil)] args)))

(defn- bin [ctx env op [a b :as args]]
  (when-not (= 2 (count args)) (outside "primitive arity"))
  (tm :prim (prim-op op) (quote* ctx env a) (quote* ctx env b)))

(defn- not* [x] (tm :if x (tm :lit [1 false]) (tm :lit [1 true])))

(defn- swapped
  "(op b a) evaluating a before b, as Clojure does: (let [x a y b] (op y x))."
  [ctx env op [a b :as args] wrap]
  (when-not (= 2 (count args)) (outside "primitive arity"))
  (tm :let (quote* ctx env a)
      (tm :let (quote* ctx (conj env '_a) b)
          (wrap (tm :prim (prim-op op) (tm :var 0) (tm :var 1))))))

(defn- quote-handle [ctx env [handlers thunk]]
  (let [pairs (cond
                (= :const (:op handlers)) (mapv (fn [[k x]] [k (t/const x)]) (:value handlers))
                (and (= :app (:op handlers)) (= 'clojure.core/hash-map (get-in handlers [:fn :name])))
                (mapv vec (partition 2 (map (fn [a] (if (= :const (:op a)) (:value a) a)) (:args handlers))))
                :else (outside "handlers must be a literal map"))
        ret (some (fn [[k x]] (when (= :return k) x)) pairs)
        clauses (remove (fn [[k _]] (= :return k)) pairs)
        _ (when-not (every? keyword? (map first clauses)) (outside "handler keys must be keywords"))
        ops (apply list (map #(intern! (:kws ctx) %) (map first clauses)))
        ;; o binds op (2), argument (1), k (0); a clause (fn [k x] ..) is applied to k then x
        env3 (conj env '_op '_arg '_k)
        call (fn [clause]
               (let [c (quote* ctx env3 clause)
                     n (count (:params (first (:arities clause))))]
                 (case n
                   1 (tm :app c (tm :var 0))
                   2 (tm :app (tm :app c (tm :var 0)) (tm :var 1))
                   (outside "handler clause arity"))))
        o (reduce (fn [else [op clause]]
                    (tm :if (tm :prim (prim-op :eq) (tm :var 2) (tm :lit (datum ctx op)))
                        (call clause) else))
                  (tm :app (tm :lit [0]) (tm :lit [0]))
                  (reverse clauses))
        r (if ret (tm :app (quote* ctx (conj env '_v) ret) (tm :var 0)) (tm :var 0))
        body (curry ctx env (quote* ctx env thunk) [])]
    (tm :handle ops body r o)))

(defn- quote-host-call [ctx env q args]
  (case q
    clojure.core/+ (bin ctx env :add args)
    (clojure.core/- klara.core/-) (bin ctx env :sub args)
    clojure.core/* (bin ctx env :mul args)
    clojure.core/= (bin ctx env :eq args)
    clojure.core/< (bin ctx env :lt args)
    clojure.core/> (swapped ctx env :lt args identity)
    clojure.core/<= (swapped ctx env :lt args not*)
    clojure.core/inc (tm :prim (prim-op :add) (quote* ctx env (first args)) (tm :lit [2 1]))
    clojure.core/dec (tm :prim (prim-op :sub) (quote* ctx env (first args)) (tm :lit [2 1]))
    ;; zero? requires a number: (= (- x 0) 0) fails on non-numbers like Clojure
    clojure.core/zero? (tm :prim (prim-op :eq)
                           (tm :prim (prim-op :sub) (quote* ctx env (first args)) (tm :lit [2 0]))
                           (tm :lit [2 0]))
    clojure.core/not (not* (quote* ctx env (first args)))
    klara.effect/perform (let [[op & xs] args]
                           (when-not (and (= :const (:op op)) (keyword? (:value op)) (<= (count xs) 1))
                             (outside "perform needs a constant keyword and at most one argument"))
                           (tm :perform (intern! (:kws ctx) (:value op))
                               (if (seq xs) (quote* ctx env (first xs)) (tm :lit [0]))))
    klara.effect/handle* (quote-handle ctx env args)
    klara.stage/lift (tm :app (tm :lam (tm :code (tm :var 0))) (quote* ctx env (first args)))
    klara.stage/run (tm :run (quote* ctx env (first args)))
    (outside "host function" :name q)))

(defn- quote* [ctx env t]
  (case (:op t)
    :const (tm :lit (datum ctx (:value t)))
    :local (tm :var (index-of env (:name t)))
    :global (let [{:keys [kind name]} (:link t)]
              (when (contains? @(:tainted ctx) name) (outside "depends on a definition outside the fragment" :name name))
              (case kind
                :late (tm :glob (intern! (:ids ctx) name))
                (outside "pinned or guarded link")))
    :fn (quote-fn ctx env t)
    :app (let [f (:fn t)]
           (cond
             (= ::esc (:name f)) (tm :esc (quote* ctx env (first (:args t))))
             (= :host (:op f)) (if (= 'clojure.core/>= (:name f))
                                 (not* (bin ctx env :lt (:args t)))
                                 (quote-host-call ctx env (:name f) (:args t)))
             :else (curry ctx env (quote* ctx env f) (:args t))))
    :recur (curry ctx env (tm :var (index-of env (:target t))) (:args t))
    :let (tm :let (quote* ctx env (:init t)) (quote* ctx (conj env (:name t)) (:body t)))
    :if (tm :if (quote* ctx env (:test t)) (quote* ctx env (:then t)) (quote* ctx env (:else t)))
    :do (let [[x & more] (:body t)]
          (if (empty? more) (quote* ctx env x)
              (tm :let (quote* ctx env x) (quote* ctx (conj env '_do) (t/do* (vec more))))))
    :letrec (let [[[n f] & more] (:bindings t)]
              (when (seq more) (outside "mutual letrec"))
              (let [{:keys [self arities]} f
                    {:keys [params rest body]} (first arities)]
                (when (or rest (not= 1 (count arities)) (empty? params)) (outside "letrec function shape"))
                (let [body (if self (t/rename body {self n}) body)]
                  (tm :letrec (lams ctx (conj env n (first params)) (next params) body)
                      (quote* ctx (conj env n) (:body t))))))
    :code (tm :code (quote* ctx env (inline-holes (:template t) (:id t) (:holes t))))
    (outside (str "term " (:op t)))))

(defn quote-term
  "Quote a closed Core term. `ctx` interns global names and keywords."
  [ctx term]
  (quote* ctx [] term))

(defn new-ctx [] {:ids (atom {}) :kws (atom {}) :tainted (atom #{})})

;; ---------------------------------------------------------------------------
;; Running the model

(defn run-model
  "Iterate `step` from config [world worlds fresh term], at most `fuel` steps."
  [world term fuel]
  (loop [c [world nil 0 term] i 0]
    (if (>= i fuel)
      {:model :fuel}
      (if-let [[c'] (f/step c)]
        (recur c' (inc i))
        (assoc (let [[w ws n t] c] {:final t :out (f/run1 w ws n t)}) :steps i)))))

(defn tm->edn
  "A de Bruijn Tm as readable data, for comparing generated code."
  [x]
  (let [[tg & fs] x nm (tag-name (int tg))]
    (case nm
      :lit (let [[dt d] (first fs)] [:lit (case (int dt) 0 nil 1 d 2 (long d) 3 [:kw d])])
      (:var :glob :gvar) [nm (long (first fs))]
      :prim [:prim (or (first fs) 0) (tm->edn (nth fs 1)) (tm->edn (nth fs 2))]
      :perform [:perform (long (first fs)) (tm->edn (second fs))]
      (:handle :handling) (into [nm (vec (first fs))] (map tm->edn (rest fs)))
      (into [nm] (map #(if (vector? %) (tm->edn %) %) fs)))))

(def ^:private stuck-name {0 :scope 1 :not-fn 2 :prim-type 3 :overflow 4 :unbound 5 :stage 6 :extrusion})

(defn observe-model [{:keys [final out model]} ctx]
  (if model
    {:model model}
    (case (int (first out))
      0 (let [[tg & fs] final]
          (case (tag-name (int tg))
            :lit (let [[dt d] (first fs)]
                   {:value (case (int dt) 0 nil 1 d 2 (long d)
                             3 (get (zipmap (vals @(:kws ctx)) (keys @(:kws ctx))) d))})
            (:lam :fix) {:value :fn}
            :code (let [d (f/toDB (first fs))]
                    (if (f/wsb 0 d) {:code (tm->edn d)} {:stuck :extrusion}))))
      2 {:stuck :unhandled}
      3 {:stuck (stuck-name (int (first (second out))))}
      4 {:stuck :extrusion})))

;; ---------------------------------------------------------------------------
;; Observing the implementation

(defn observe-impl [result ctx]
  (if-let [e (:error result)]
    (let [rule (:rule (ex-data e))
          msg (str (.getMessage ^Throwable e))]
      (cond
        (#{:L2.code.extrusion :L2.run.closed} rule) {:stuck :extrusion}
        (= :L2.esc.not-code rule) {:stuck :stage}
        (= :L3.effect.unhandled rule) {:stuck :unhandled}
        (= :L1.resolve.unbound rule) {:stuck :unbound}
        ;; the model curries: arity errors are outside its fragment
        (= :L0.eval.arity rule) {:outside :arity}
        (= :L0.eval.not-fn rule) {:stuck :not-fn}
        (instance? ArithmeticException e) {:stuck :overflow}
        (and (instance? ClassCastException e) (re-find #"IFn" msg)) {:stuck :not-fn}
        (or (instance? ClassCastException e) (instance? NullPointerException e)) {:stuck :prim-type}
        :else {:error (str (class e) ": " msg) :rule rule}))
    (let [x (:value result)]
      (cond
        (or (nil? x) (boolean? x) (integer? x) (keyword? x)) {:value (if (integer? x) (long x) x)}
        (v/code? x) (try {:code (tm->edn (quote-term ctx (.-term ^Code x)))}
                         (catch clojure.lang.ExceptionInfo e (if (outside? e) {:outside :code-value} (throw e))))
        (coll? x) {:outside :value}
        (or (v/closure? x) (fn? x) (instance? clojure.lang.IFn x)) {:value :fn}
        :else {:outside :value}))))

;; ---------------------------------------------------------------------------
;; Differential comparison over source

(defn- directive? [term]
  (and (= :app (:op term)) (= :host (get-in term [:fn :op]))
       (= "klara.kernel" (namespace (get-in term [:fn :name])))))

(defn- elements
  "The element terms of a top-level vector, compared one by one (the model
   has no collections)."
  [term]
  (when (and (= :app (:op term)) (= 'clojure.core/vector (get-in term [:fn :name])))
    (:args term)))

(defn- observe-terms [els world ctx fuel]
  (if els
    (mapv #(observe-model (run-model world (quote-term ctx %) fuel) ctx) els)
    ::single))

(defn- agree?
  "A vector agrees elementwise; if the implementation failed, the first
   failing element of the model must fail the same way."
  [io mo]
  (cond
    (vector? io) (= io mo)
    (vector? mo) (if (:stuck io) (= io (first (filter :stuck mo))) false)
    :else (= io mo)))

(defn compare-source
  "Evaluate `src` form by form in a fresh session and in the model. Returns
   a vector of {:form :impl :model :agree?} for forms inside the fragment,
   and {:form :outside why} for the others."
  [src & {:keys [roots fuel] :or {roots ["lib"] fuel 2000000}}]
  (let [s (k/session {:roots roots :out (java.io.StringWriter.)})
        ctx (new-ctx)
        world (atom nil)
        r (clojure.lang.LineNumberingPushbackReader. (java.io.StringReader. src))]
    (loop [acc []]
      (let [form (ex/read-all r (:ns @s))]
        (if (ex/eof? form)
          acc
          (let [term (try (session/expand s form) (catch Throwable e {:expand-error e}))
                impl (if (:expand-error term) {:error (:expand-error term)}
                         (try {:value (session/activation s term)} (catch Throwable e {:error e})))
                entry
                (cond
                  (:expand-error term) {:form form :front-end (.getMessage ^Throwable (:expand-error term))}
                  (directive? term) nil
                  (= :def (:op term))
                  (let [q (:name term)]
                    (try
                      (let [m (run-model @world (quote-term ctx (:init term)) fuel)]
                        (if (= 0 (int (first (:out m))))
                          (do (swap! world (fn [w] [(intern! (:ids ctx) q) (:final m) w])) nil)
                          (do (swap! (:tainted ctx) conj q)
                              {:form form :impl (observe-impl impl ctx) :model (observe-model m ctx)})))
                      (catch clojure.lang.ExceptionInfo e
                        (if (outside? e)
                          (do (swap! (:tainted ctx) conj q) {:form form :outside (::outside (ex-data e))})
                          (throw e)))))
                  :else
                  (try
                    (let [els (elements term)
                          io (if (and els (vector? (:value impl)))
                               (mapv #(observe-impl {:value %} ctx) (:value impl))
                               (observe-impl impl ctx))]
                      (if (or (:outside io) (and (vector? io) (some :outside io)))
                        {:form form :outside (:outside io)}
                        (let [mo (if els (observe-terms els @world ctx fuel)
                                     (observe-model (run-model @world (quote-term ctx term) fuel) ctx))]
                          {:form form :impl io :model mo :agree? (agree? io mo)})))
                    (catch clojure.lang.ExceptionInfo e
                      (if (outside? e) {:form form :outside (::outside (ex-data e))} (throw e)))))]
            (recur (cond-> acc entry (conj entry)))))))))
