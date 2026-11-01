(ns klara.compile.kernel
  "Preparation, candidates and execution (spec/L4-compiler.md).

  The guest-facing API is klara.compiler (lib/klara/compiler.clj), written
  in Klara over the intrinsics registered here as klara.compiler.kernel/*.
  `prepare` runs a guest recipe inside a job, then the trusted checker and
  backend. An executable checks its premises at entry and otherwise runs
  the reference meaning."
  (:require [klara.compile.check :as check]
            [klara.compile.lower :as lower]
            [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.intrinsics :as intr]
            [klara.runtime.job :as job]
            [klara.runtime.machine :as m]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Closure Code]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

(defn- ret [st x] (assoc st :mode :ret :ctl x :env nil))

;; ---------------------------------------------------------------------------
;; Candidates and executables

(defrecord Candidate [name reference term premises host-fn form guards evidence])

(defn valid?
  "L4.exec.valid: every premise holds in `world`."
  [cand world]
  (every? (fn [[q g]] (= g (w/generation world q))) (:premises cand)))

(def guard-predicates
  "Argument guards a certificate can assume (L4.check.certificate)."
  {:long #(instance? Long %)})

(defn- guards-hold? [cand args]
  (let [gs (:guards cand)]
    (or (nil? gs)
        (and (= (count gs) (count args))
             (every? true? (map (fn [g x] (or (nil? g) ((guard-predicates g) x))) gs args))))))

;; Certifiers admit candidates the definitional checker cannot relate, given
;; a certificate (L4.check.certificate). A certifier returns
;; {:result :proved :guards [..] :evidence ..} or {:result :failed :message ..}.
(defonce certifiers (atom {}))

(defn register-certifier! [kind f] (swap! certifiers assoc kind f))

;; Compiled code left (L4.exec.leave); carries the leave state.
(deftype Left [leave])

(v/deftype-callable Executable [cand ^:volatile-mutable last-world ^:volatile-mutable last-valid
                                ^:volatile-mutable last-path]
  v/IExecutable
  (-execute [this st args]
    (let [world (:world st)
          ok (and (nil? (:mint st))
                  (if (identical? world last-world)
                    last-valid
                    (let [r (valid? cand world)] (set! last-world world) (set! last-valid r) r))
                  (guards-hold? cand args))
          r (if ok
              (try (m/set-context! world (:mint st) (:dyn st))
                   (apply (:host-fn cand) args)
                   (catch clojure.lang.ExceptionInfo ex
                     (if-let [l (lower/leave? ex)] (Left. @l) (throw ex))))
              ::invalid)]
      (cond
        (= ::invalid r)
        (do (set! last-path :reference)                           ; L4.exec.executable
            (assoc st :mode :apply
                   :ctl [(m/closure-of (.-term ^Code (:reference cand)) (:mint st)) (vec args)]))
        (instance? Left r)
        (do (set! last-path :left)                                 ; L4.exec.leave
            (lower/resume st (.-leave ^Left r)))
        :else (do (set! last-path :compiled) (ret st r)))))
  (-call [this world mint dyn args]
    (if (and (nil? mint)
             (if (identical? world last-world)
               last-valid
               (let [r (valid? cand world)] (set! last-world world) (set! last-valid r) r))
             (guards-hold? cand args))
      (do (set! last-path :compiled) (apply (:host-fn cand) args))
      v/fallback))
  (-describe [this]
    {:name (:name cand) :reference (:reference cand) :premises (:premises cand)
     :guards (:guards cand) :evidence (:evidence cand)
     :compiled (:form cand) :last-path last-path})
  Object
  (toString [_] (str "#klara/executable[" (or (:name cand) "anonymous") "]")))

(defmethod print-method Executable [x ^java.io.Writer out] (.write out (str x)))

(defn executable [cand] (Executable. cand nil false nil))

(defn- candidate-of [^Executable e] (.-cand e))

;; ---------------------------------------------------------------------------
;; Dispatch table (L4.exec.install, L4.retain.dispatch)

(def candidates-per-name 4)

(defn install! [session cand]
  (let [q (:name cand)]
    (when-not q (fail :L4.exec.install "only a candidate for a named definition can be installed"))
    (.incrementAndGet m/dispatch-epoch)        ; invalidate globals' inline caches
    (swap! session update-in [:dispatch q]
           (fn [xs] (vec (take candidates-per-name
                               (cons (executable cand) (remove #(= (:term (candidate-of %)) (:term cand)) xs))))))
    q))

(reset! m/resolve-hook
        (fn [q _d world session]
          (when-let [xs (get-in @session [:dispatch q])]
            (some #(when (valid? (candidate-of %) world) %) xs))))

;; ---------------------------------------------------------------------------
;; Preparation (L4.prepare.job)

(defn- reject [rule message & {:as more}]
  (merge {:status :rejected :rule rule :message message} more))

(defn- finish
  "Check and lower `candidate` against `reference`, inside the job (state `st`)."
  [st reference candidate opts]
  (if-not (v/code? candidate)
    (reject :L4.prepare.recipe-failed (str "the recipe returned " (pr-str candidate) ", not code"))
    (let [ref-term (.-term ^Code reference)
          cand-term (.-term ^Code candidate)
          r (check/check ref-term cand-term (:world st) (get-in st [:dyn :meter]))
          r (if-let [cert (and (= :different (:result r)) (:certificate opts))]
              (if-let [certify (get @certifiers (:kind cert))]
                (let [c (certify {:reference ref-term :candidate cand-term :world (:world st) :certificate cert})]
                  (if (= :proved (:result c))
                    {:result :equal :premises #{} :guards (:guards c) :evidence (:evidence c)}
                    {:result :certificate-failed :message (:message c)}))
                {:result :certificate-failed :message (str "no certifier for " (pr-str (:kind cert)))})
              r)]
      (case (:result r)
        :certificate-failed (reject :L4.check.certificate (str "the certificate was not accepted: " (:message r)))
        :exhausted {:status :exhausted :rule :L4.check.exhausted
                    :message "the checker ran out of budget before deciding"}
        :different (reject :L4.check.not-equivalent
                           (str "candidate differs from the reference: "
                                (pr-str (second (:difference r))) " vs " (pr-str (first (:difference r))))
                           :difference (:difference r)
                           :hint "the checker unfolds definitions, substitutes values and folds constants; it does not use algebraic identities")
        :equal (if-let [x (lower/subset-violation cand-term)]
                 (reject :L4.lower.subset (str "the backend does not compile " x))
                 (let [premises (cond-> (:premises r)
                                  (:name opts) (conj [(:name opts) (w/generation (:world st) (:name opts))]))
                       {:keys [fn form]} (lower/lower cand-term {:self-name (:name opts)})]
                   {:status :ready
                    :candidate (->Candidate (:name opts) reference cand-term premises fn form
                                            (:guards r) (:evidence r))
                    :premises (vec (sort-by (comp str first) premises))
                    ;; how equivalence was established (design/05-specialization.md)
                    :evidence (or (:evidence r) :definitional)
                    :speculations (count (filter #(and (= :if (:op %)) (:speculate %)) (t/nodes cand-term)))}))))))

(defn- settle
  "Turn the job outcome around preparation into a preparation outcome."
  [st outcome]
  (ret st (case (:status outcome)
            :done (assoc (:value outcome) :spent (:spent outcome))
            :exhausted {:status :exhausted :rule :L3.budget.exhausted :spent (:spent outcome)
                        :message "the recipe ran out of budget"}
            :failed (reject :L4.prepare.recipe-failed
                            (str "the recipe failed: " (get-in outcome [:error :message]))
                            :error (:error outcome) :spent (:spent outcome)))))

(b/register! 'klara.compiler.kernel/prepare
  {:kind :intrinsic
   :fn (fn [st [reference opts]]
         (when-not (v/code? reference) (fail :L4.prepare.reference "the reference must be code"))
         (when-not (= :fn (:op (.-term ^Code reference)))
           (fail :L4.prepare.reference "the reference must be code for a function"))
         (let [opts (or opts {})
               recipe (or (:recipe opts) identity)
               st (assoc st :k (conj (:k st) {:f :frame-fn :fn settle}))
               st (job/start st {:budget (or (:budget opts) {:steps 100000})})]
           (assoc st :mode :apply :ctl [recipe [reference]]
                  :k (conj (:k st) {:f :frame-fn
                                    :fn (fn [st cand] (ret st (finish st reference cand opts)))}))))})

(b/register! 'klara.compiler.kernel/executable
  {:kind :intrinsic
   :fn (fn [st [outcome]]
         (when-not (= :ready (:status outcome))
           (fail :L4.exec.executable (str "no candidate: the outcome is " (:status outcome))))
         (ret st (executable (:candidate outcome))))})

(b/register! 'klara.compiler.kernel/install!
  {:kind :intrinsic
   :fn (fn [st [outcome]]
         (when-not (= :ready (:status outcome))
           (fail :L4.exec.install (str "no candidate: the outcome is " (:status outcome))))
         (ret st (install! (get-in st [:dyn :session]) (:candidate outcome))))})

(b/register! 'klara.compiler.kernel/reference
  {:kind :intrinsic
   :fn (fn [st [q]]
         (let [d (w/lookup (:world st) q)]
           (when-not (and d (v/closure? (:value d)))
             (fail :L4.prepare.reference (str q " is not a function definition")))
           (ret st (intr/reify-closure (:value d)))))})

(b/register! 'klara.compiler.kernel/pin
  {:kind :intrinsic
   :fn (fn [st [c world]] (ret st (Code. (intr/pin-links (.-term ^Code c) world))))})

(b/register! 'klara.compiler.kernel/explain
  {:kind :intrinsic
   :fn (fn [st [f]]
         (ret st (cond
                   (instance? Executable f)
                   (assoc (v/-describe f) :valid (valid? (candidate-of f) (:world st)))
                   (v/closure? f) {:kind :interpreted :code (intr/reify-closure f)}
                   :else {:kind :host :value f})))})

(b/register! 'klara.compiler.kernel/arity
  {:kind :intrinsic
   :fn (fn [st [f]]
         (ret st (when (v/closure? f)
                   (mapv (fn [a] (cond-> (count (:params a)) (:rest a) (vector :&)))
                         (:arities (.-term ^Closure f))))))})

(b/register! 'klara.compiler.kernel/specialization
  {:kind :intrinsic
   :fn (fn [st [f known]]
         ;; (fn [u..] (f k-or-u ..)) for a closure of fixed arity n (L4: specialize)
         (let [n (some #(when (nil? (:rest %)) (count (:params %))) (:arities (.-term ^Closure f)))
               ps (vec (for [i (range n) :when (not (contains? known i))] (t/fresh (str "a" i))))
               args (loop [i 0 ps ps out []]
                      (if (= i n) out
                          (if (contains? known i)
                            (recur (inc i) ps (conj out (m/lift-term (get known i))))
                            (recur (inc i) (rest ps) (conj out (t/local (first ps)))))))]
           (ret st (Code. (t/fn-term nil [(t/arity ps nil (t/app (m/lift-term f) args))])))))})

(b/register! 'klara.compiler.kernel/normalize
  {:kind :intrinsic
   :fn (fn [st [c]]
         (if-let [n (check/normalize (.-term ^Code c) (:world st) (get-in st [:dyn :meter]))]
           (ret st (Code. n))
           (m/abandon! :exhausted)))})

;; ---------------------------------------------------------------------------
;; klara.jit: building speculations (L4.check.speculate, L4.exec.leave)

(b/register! 'klara.jit/guard
  {:kind :host
   :fn (fn [guard specialized reference]
         (Code. (t/refresh-free {:op :if :speculate true
                                 :test (.-term ^Code guard)
                                 :then (.-term ^Code specialized)
                                 :else (.-term ^Code reference)})))})

(defn- runtime-info
  "Host facts a specializer may use (design/06-speculation.md#6-specializers)."
  []
  {:host :jvm
   :java (System/getProperty "java.version")
   :processors (.availableProcessors (Runtime/getRuntime))})

(b/register! 'klara.jit/context                                       ; L4.jit.context
  {:kind :intrinsic
   :fn (fn [st [q]]
         (let [world (:world st)
               d (w/lookup world q)
               f (:value d)]
           (when-not (and d (v/closure? f))
             (fail :L4.jit.context (str q " is not a function definition")))
           (let [s (get-in d [:meta :klara/specialize])
                 sq (when s (if (namespace s) s (symbol (namespace q) (name s))))
                 specializer (when sq
                               (or (:value (w/lookup world sq))
                                   (fail :L4.jit.attach (str "specializer " sq " is not defined"))))]
             (ret st {:name q
                      :reference (intr/reify-closure f)
                      :profile (intr/profile-snapshot f)
                      :runtime (runtime-info)
                      :specializer specializer}))))})

(b/register! 'klara.jit/function                                      ; L4.jit.function
  {:kind :intrinsic
   :fn (fn [st [ctx f]]
         ;; (fn [p..] (f p..)) with fresh parameters, for the definition's arity;
         ;; the parameters count as bound while f builds the body (L2.code.extrusion)
         (let [params (:params (intr/view (:reference ctx)))
               fresh (mapv #(t/fresh (t/base-name %)) params)
               build (fn [st body]
                       (when-not (v/code? body)
                         (fail :L4.jit.function (str "the body function returned " (pr-str body) ", not code")))
                       (ret st (Code. (t/refresh-free (t/fn-term nil [(t/arity fresh nil (.-term ^Code body))])))))
               k (:k st)]
           (assoc st :mode :apply
                  :ctl [f (mapv #(Code. (t/local %)) fresh)]
                  :k (conj k {:f :frame-fn :fn build}
                             {:f :binders :bound (into (m/constructing k) fresh)}))))})
