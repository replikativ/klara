(ns klara.eval
  "T0: the reference interpreter of Klara Core K0 — the executable draft
  of the specification. Clarity over speed.

  A CEK machine. The state is [mode control env kont]:
    mode :eval  control is a term to evaluate,
    mode :ret   control is a value returning into kont.
  env is {:locals [v ..] :basis root :mint root|nil}; kont is a list of
  frames (top first). Every frame is plain data, so a captured
  continuation is a vector of frames and resuming it pushes them back:
  handlers are deep, resumption is multi-shot. Calls in tail position
  push no frame, so self tail calls through letrec run in constant space
  (doc/interpreters.md).

  AUTHORITY (RFC 0001, S6; the store and split rules are klara.authority).
  - Resuming a continuation a SECOND time is fork-resume: it is refused
    when the continuation captured a resource or evidence authority or
    an open fork (found by walking its frames: locals, collections,
    metadata, closures, nested continuations), and otherwise runs under
    a :shot branch context, which splits the other kinds when they are
    used (so an authority reached by a lookup after capture is checked
    at its use).
  - (perform :auth/fork opts thunks body) runs each thunk under a
    {:tag :branch} frame of its own context, then the body with the
    branch values under a {:tag :fork-scope} frame; returning through the
    scope settles the group (adopted branch merged, others discarded).
    An exception unwinding through a branch or scope frame discards the
    group before it propagates (cancellation).
  - An irreversible host call (klara.authority/irreversible?) reaching
    the reference handler inside a fork branch is deferred as an intent;
    under a {:tag :direct} frame it runs and leaves a receipt.

  EFFECTS (RFC 0002).
  - (handle :lexical ...) creates a fresh handler INSTANCE, binds it in
    the body and pushes a handle frame carrying its id. (perform inst op)
    searches the continuation for that id only, so a library handler in
    between can never intercept it (EF4).
  - Ambient operations (:world/* :host/* :exn/* :time/*) are performed
    without a target and found by dynamic search for the nearest
    (handle :dynamic ...) frame with a clause for the op; if there is
    none, the REFERENCE HANDLER answers (below). An uncaught :exn/raise
    leaves the machine as a host exception.
  - A clause is a function of the operation's arguments plus the
    continuation k. Not calling k aborts to the handle frame; calling it
    resumes with the handler reinstalled.
  - Host exceptions raised by prims or host calls become :exn/raise at
    the point of the call. A Klara closure called BY host code (e.g. a fn
    passed to clojure.core/map) runs in a nested machine: its continuation
    stops at the host frame, so a lexical perform from inside cannot reach
    an outer handler and is reported as an error at the boundary (EF5).

  GLOBALS AND BASES (§3). A closure carries the basis it was created
  under; `resolve` inside it reads that basis. World definitions are
  stored as OPEN closures (basis nil): they run under the basis of
  whoever resolved them. That is what makes execution basis-specific:
  there is no shared host namespace, so a parent's g calling f never sees
  a fork's f (the X1 leak). :mint is the basis stamped on new closures;
  definition-time evaluation runs with :mint nil, so the closures a
  definition creates stay open.

  SPECIALIZE has its reference meaning: (specialize f a ..) is a partial
  application value (s-m-n). On entry to a closure or partial application
  the optional *entry-hook* (klara.stage) may supply an executable whose
  guards hold; otherwise the generic path runs.

  DEOPT (S7). A speculative executable carries frame states (see
  `materialize`). Its Klara code runs under an {:tag :exe} marker frame
  (pushed once: a self tail call through the hook finds it on top and
  pushes nothing, so loops stay in constant space); (perform :stage/deopt
  i live) drops the residual's frames down to the marker and continues
  with the generic state rebuilt from frame state i. A host executable
  leaves by klara.eval/deopt!. Effects performed before the guard are
  not repeated: generic execution resumes at the guard's position."
  (:require [clojure.main]
            [clojure.string]
            [klara.authority :as a]
            [klara.effect-class :as effect-class]
            [klara.core :as core]
            [klara.code :as code]
            [klara.world :as w]))

(def ^:dynamic *fiber* nil)
(def ^:dynamic *basis* nil)
(def ^:dynamic *mint* nil)
(def ^:dynamic *direct-hook* nil)
(def ^:dynamic *context-hook* nil)
(def ^:dynamic *entry-hook*
  "nil, or (fn [f statics args basis kont]) -> executable map or nil.
  kont is the caller's continuation (frames top first), so guards can
  inspect the handler context the call runs in."
  nil)

(def ^:dynamic *deopt-hook*
  "nil, or (fn [exe frame-state live]) called on every deopt (klara.stage
  counts it as feedback)."
  nil)

(defn deopt!
  "Called by a host executable at a failed guard: resume generic T0 at
  the executable's frame state i with the live values live."
  [i live]
  (throw (ex-info "klara: deopt" {::deopt [i (vec live)]})))

(defonce ^{:doc "Returned by a host executable (:run) to decline at entry: the
  generic path then runs from the start. Only sound for executables that
  performed no effect before declining (host executables perform none)."}
  deopt (Object.))

(declare call-value call-value* locus-rec-call stage-perform auth-perform start-code step-build
         step-ret-stage all-frames resume-blocker close-then-ret fork-continue cleanup-captured!)

(defmacro ^:private ifn-via-call-value []
  `(~@(for [n (range 9)
            :let [args (vec (repeatedly n gensym))]]
        `(~'invoke [~'this ~@args] (call-value ~'this ~args)))
    (~'applyTo [~'this ~'xs] (call-value ~'this (vec ~'xs)))))

(defmacro ^:private deftype-ifn [name fields & body]
  `(deftype ~name ~fields
     clojure.lang.IFn
     ~@(macroexpand-1 `(ifn-via-call-value))
     ~@body))

;; Closure: code + captured locals (a vector, or a delay of one for
;; letrec) + creation basis (nil = open).
(deftype-ifn Closure [term env basis])
;; Partial application: the reference meaning of specialize.
(deftype-ifn Pap [f statics])

(defrecord Cont [frames shots])           ; shots: atom counting resumptions
(defrecord Instance [id mode])
;; The memoizing generator bound by with-genletrec (genletrec, S4).
(deftype LocusRec [id])

(defn closure? [x] (instance? Closure x))
(defn closure-term [^Closure c] (.-term c))
(defn closure-locals [^Closure c] (force (.-env c)))
(defn closure-basis [^Closure c] (.-basis c))
(defn rebase
  "An open closure bound to basis b; other values unchanged."
  [v b]
  (if (and (closure? v) (nil? (closure-basis v)) b)
    (Closure. (closure-term v) (.-env ^Closure v) b)
    v))
(defn pap? [x] (instance? Pap x))
(defn pap-fn [^Pap p] (.-f p))
(defn pap-statics [^Pap p] (.-statics p))

;; ---------------------------------------------------------------------------
;; environment
;; ---------------------------------------------------------------------------

(defn- lookup [env i]
  (let [ls (:locals env)] (nth ls (- (count ls) 1 i))))

(defn- push [env v] (update env :locals conj v))

;; ---------------------------------------------------------------------------
;; raising and performing
;; ---------------------------------------------------------------------------

(declare do-perform)

(defn- raise [ex env k] (do-perform nil :exn/raise [ex] env k))

(def ^:dynamic *outer-k*
  "Continuations of the machines suspended behind host frames, innermost
  first. A Klara closure called by host code (map, reduce, ..) runs in a
  nested machine; staging consults these frames so that code built in
  such a callback still sees the binders and let-insertion loci of the
  code being generated around the host call (S4)."
  ())

(defn- host-apply [f args env k]
  (try [:ret (binding [*outer-k* (conj *outer-k* k)] (apply f args)) env k]
       (catch Throwable t (raise t env k))))

(defn- host-var [sym]
  (or (and (qualified-symbol? sym) (requiring-resolve sym))
      (throw (ex-info (str "klara: no host var " sym) {:sym sym}))))

(def reference-handlers
  "The ambient reference handlers: tail-resumptive, called directly with
  the operation's arguments and the machine env. :exn/raise is handled
  in do-perform (uncaught = leave the machine)."
  {:host/call (fn [[sym & args] _] (apply @(host-var sym) args))
   :host/var  (fn [[sym] _] @(host-var sym))
   :host/static-field (fn [[cls f] _]
                        (clojure.lang.Reflector/getStaticField ^Class (resolve cls) (name f)))
   :host/static (fn [[cls m & args] _]
                  (clojure.lang.Reflector/invokeStaticMethod
                   ^Class (resolve cls) (name m) (object-array args)))
   :host/class (fn [[sym] _]
                 (let [c (resolve sym)]
                   (if (class? c) c (throw (ex-info "klara: no class" {:sym sym})))))
   :world/version (fn [_ env] (:version (:basis env)))
   :world/resolve (fn [[sym] _]
                    (let [b (w/basis *fiber*)]
                      (rebase (:value (w/entry* b sym)) b)))
   :world/raise-basis (fn [_ _] (:version (w/raise-basis! *fiber*)))
   :world/define (fn [[sym v] _]
                   (let [generation (w/fresh-value-id)]
                     (:version
                      (w/publish! (:world *fiber*)
                                  #(w/put-entry % sym {:kind :def :value v :reads #{}
                                                       :code-id (str "runtime:" generation)
                                                       :value-id generation})))))})

(defonce ^{:private true :doc "Reference handlers registered by namespaces that
  sit above eval (klara.defs registers the world operations that need the
  expander)."} extra-handlers (atom {}))

(defn register-reference-handler!
  "Add the reference handler for ambient operation op: (fn [args env])."
  [op f]
  (assert (core/ambient? op))
  (swap! extra-handlers assoc op f)
  op)

(defn- find-frame
  "Split kont at the first handle frame satisfying pred:
  [captured-frames-top-first outer-kont frame] or nil."
  [k pred]
  (loop [k k captured []]
    (when (seq k)
      (let [f (peek k)]
        (if (and (= :handle (:tag f)) (pred f))
          [(conj captured f) (pop k) f]
          (recur (pop k) (conj captured f)))))))

(defn- unwind-frame? [f] (contains? #{:branch :fork-scope :borrow :capture-exit} (:tag f)))

(defn- find-raise-frame
  "Split kont at the first dynamic handler of :exn/raise or the first
  branch/scope frame an exception must settle on its way out."
  [k]
  (loop [k k captured []]
    (when (seq k)
      (let [f (peek k)]
        (cond
          (and (= :handle (:tag f)) (= :dynamic (:mode f)) (contains? (:clauses f) :exn/raise))
          [(conj captured f) (pop k) f]
          (unwind-frame? f) [nil (pop k) f]
          :else (recur (pop k) (conj captured f)))))))

(defn- unwind!
  "Settle the fork group of an unwind frame passed by an exception: a
  fork is discarded, a shot ends."
  [f outer]
  (let [frames (all-frames outer)]
    (case (:tag f)
      :borrow (when (= :open (:status (a/state (:loan f)))) (a/return-owned! (:loan f)))
      :capture-exit (cleanup-captured! (:frames f) outer)
      :branch (let [ctx (:ctx f)]
        (a/close-group! (:group ctx) frames (if (= :shot (:mode ctx)) :exit :abort)))
      (a/close-group! (:group f) frames :abort))))

(defn- cleanup-captured! [frames outer]
  (doseq [f frames :when (unwind-frame? f)]
    (when (or (#{:borrow :capture-exit} (:tag f))
              (and (:group f) (a/group-open? (:group f)))
              (and (:ctx f) (a/ctx-open? (:ctx f))))
      (unwind! f outer))))

(defn- dispatch-clause [cl args captured outer env k op]
  (let [kind (when (closure? cl) (effect-class/classify (closure-term cl)))
        borrowed? (some #(= :borrow (:tag %)) captured)]
    (if (and (not (#{:tail :abortive} kind)) (a/full-owned-held? (all-frames k)))
      (let [error (ex-info "klara: general effect cannot capture a full owned write share"
                           {:klara/error :authority})]
        ;; A rejected exception clause cannot catch its own admission error.
        (if (= op :exn/raise)
          (do (when borrowed? (cleanup-captured! captured outer)) (raise error env outer))
          (raise error env k)))
      (if (= :abortive kind)
        (do (when borrowed? (cleanup-captured! captured outer))
            (call-value* cl (conj (vec args) nil) env outer))
        (call-value* cl (conj (vec args) (->Cont captured (atom 0))) env
                     (cond-> outer borrowed? (conj {:tag :capture-exit :frames captured :env env})))))))

(defn- reference-call
  "Run reference handler h. An irreversible host call is deferred inside
  a fork branch and leaves a receipt under a capability (RFC 0001)."
  [h op args env k]
  (let [[m x] (when (and (= :host/call op) (a/irreversible? (first args)))
                (a/effect-mode (all-frames k)))]
    (if (= :defer m)
      [:ret (a/defer! x op args) env k]
      (try (when (= :direct m) (a/direct-receipt! x (first args) (rest args)))
           [:ret (h args env) env k]
           (catch Throwable t (raise t env k))))))

(defn- do-perform [target op args env k]
  (if target
    (if-let [[captured outer f] (and (instance? Instance target)
                                     (find-frame k #(= (:id target) (:id %))))]
      (if-let [cl (get (:clauses f) op)]
        (dispatch-clause cl args captured outer env k op)
        (raise (ex-info (str "klara: instance does not handle " op) {:op op}) env k))
      (raise (ex-info (str "klara: unhandled lexical effect " op
                           " (instance out of extent, or behind a host frame)")
                      {:op op :klara/error :unhandled}) env k))
    (if-let [[captured outer f]
             (if (= :exn/raise op)
               (find-raise-frame k)
               (find-frame k #(and (= :dynamic (:mode %)) (contains? (:clauses %) op))))]
      (if (unwind-frame? f)
        (do (try (unwind! f outer) (catch clojure.lang.ExceptionInfo _ nil))
            (do-perform nil op args env outer))
        (dispatch-clause (get (:clauses f) op) args captured outer env k op))
      (if (= :exn/raise op)
        (let [ex (first args)]
          (throw (if (instance? Throwable ex)
                   ex
                   (ex-info "klara: uncaught exception" {:klara/exn ex}))))
        (if-let [h (or (reference-handlers op) (@extra-handlers op))]
          (reference-call h op args env k)
          (raise (ex-info (str "klara: no handler for " op) {:op op}) env k))))))

;; ---------------------------------------------------------------------------
;; application
;; ---------------------------------------------------------------------------

(defn- enter-hook [f statics args basis k]
  (or (when (and *direct-hook* (empty? statics)
                 (not-any? #(and (= :handle (:tag %)) (= :dynamic (:mode %))) k))
        (*direct-hook* f args basis))
      (when *entry-hook* (*entry-hook* f statics args basis k))))

(defn- enter-closure
  "The generic path: bind arguments, run the body under the closure's
  basis (or the caller's, for an open closure)."
  [f args env k]
  (let [{:keys [arity rest? body]} (closure-term f)
        n (count args)]
    (if (or (< n arity) (and (not rest?) (> n arity)))
      (raise (ex-info "klara: arity mismatch" {:expected arity :rest? rest? :actual n})
             env k)
      (let [av (vec args)
            bound (if rest? (conj (subvec av 0 arity) (seq (subvec av arity))) av)]
        [:eval body {:locals (into (closure-locals f) bound)
                     :basis (or (closure-basis f) (:basis env))
                     :mint (or (closure-basis f) (:mint env))}
         k]))))

(declare materialize drive invoke-boxed)

(defn- exe-frame
  "k with the marker of speculative executable exe on top (unless the
  same marker already is: a tail call into exe again)."
  [exe k]
  (let [f (peek k)]
    (if (and f (= :exe (:tag f)) (identical? (:frame-states exe) (:frame-states (:exe f))))
      k
      (conj k {:tag :exe :code-id (:code-id exe) :exe exe}))))

(defn- deopt-state
  "The generic machine state for deopt i of exe with live values, over
  continuation k; env supplies the basis and mint."
  [exe i live env k]
  (if-let [fs (get (:frame-states exe) i)]
    (do (when *deopt-hook* (*deopt-hook* exe fs live))
        (materialize (:generic exe) fs live env k))
    (raise (ex-info (str "klara: no frame state " i) {:klara/error :stage}) env k)))

(defn- run-executable
  "An executable either names Klara code entered in THIS machine
  (:klara closure + :prefix arguments; effects keep working) or a host
  function (:run; a host frame, so it must not perform Klara effects).
  A host function may return `deopt`; then generic, a thunk producing the
  generic machine state, runs instead (replay from entry, so only sound
  before any effect). It may also call deopt! at a frame state; then
  generic T0 resumes there, in genv (the env the generic code would
  have had: its basis and mint)."
  [exe args env k generic genv]
  (if-let [g (:klara exe)]
    (enter-closure g (into (vec (:prefix exe)) args) env
                   (if (:frame-states exe) (exe-frame exe k) k))
    (let [r (try [:ok (binding [*outer-k* (conj *outer-k* k)
                                *basis* (:basis genv) *mint* (:mint genv)]
                         (invoke-boxed (:run exe) args))]
                 (catch Throwable t [:exn t]))
          v (nth r 1)]
      (if (= :ok (nth r 0))
        (if (identical? deopt v)
          (do (some-> (:deopts exe) (swap! inc)) (generic))
          [:ret v env k])
        (if-let [[i live] (::deopt (ex-data v))]
          (deopt-state exe i live genv k)
          (raise v env k))))))

(defrecord CallContext [basis mint outer-k cache feedback])

(defn invoke-boxed
  "Fixed public IFn calls for common boxed arities; retain the seq adapter."
  [f args]
  (case (count args)
    0 (f) 1 (f (nth args 0)) 2 (f (nth args 0) (nth args 1))
    3 (f (nth args 0) (nth args 1) (nth args 2))
    4 (f (nth args 0) (nth args 1) (nth args 2) (nth args 3))
    (apply f args)))

(defn record-executable-reads! [exe]
  ;; The compiler already records this transitive set at entry. Repeating
  ;; its elements at every nested call adds nothing to the recorded set.
  (when w/*reads* (doseq [r (:definition-reads exe)] (w/note-read! r))))

(defn resume-context [ctx exe f args failure]
  ;; Cold bridge: materialization and arbitrary T0/host callbacks still use
  ;; the public dynamic context, with the original authority frame objects.
  (binding [*basis* (:basis ctx) *mint* (:mint ctx) *outer-k* (:outer-k ctx)]
    (if failure
      (let [[i live] failure]
        (drive (deopt-state exe i live {:basis (:basis ctx) :mint (:mint ctx)} '())))
      (drive (enter-closure f args {:basis (:basis ctx) :mint (:mint ctx)} '())))))

(defmacro ^:private define-context-invoker []
  `(defn ~'invoke-context
     ~@(for [n (range 5)
             :let [ps (mapv #(symbol (str "a" %)) (range n))]]
         `([~'ctx ~'exe ~'f ~@ps]
           (try
             (let [v# ((:invoke ~'exe) ~'ctx ~@ps)]
               (if (identical? deopt v#)
                 (resume-context ~'ctx ~'exe ~'f [~@ps] nil) v#))
             (catch clojure.lang.ExceptionInfo t#
               (if-let [failure# (::deopt (ex-data t#))]
                 (resume-context ~'ctx ~'exe ~'f [~@ps] failure#)
                 (throw t#))))))))

(define-context-invoker)

(defn invoke-direct
  "ABI v1 host boundary, with an optional explicit compiled context.
  Only cold deopt/decline constructs a machine; each callee owns its exit."
  ([exe f args] (invoke-direct (when *context-hook* (*context-hook*)) exe f args))
  ([ctx exe f args]
   (if (and ctx (:invoke exe) (<= (count args) 4))
     (do
       (record-executable-reads! exe)
       (case (count args)
         0 (invoke-context ctx exe f)
         1 (invoke-context ctx exe f (nth args 0))
         2 (invoke-context ctx exe f (nth args 0) (nth args 1))
         3 (invoke-context ctx exe f (nth args 0) (nth args 1) (nth args 2))
         4 (invoke-context ctx exe f (nth args 0) (nth args 1) (nth args 2) (nth args 3))))
     (try
       (let [v (invoke-boxed (:run exe) args)]
         (if (identical? deopt v)
           (drive (enter-closure f args {:basis *basis* :mint *mint*} '())) v))
       (catch clojure.lang.ExceptionInfo t
         (if-let [[i live] (::deopt (ex-data t))]
           (drive (deopt-state exe i live {:basis *basis* :mint *mint*} '()))
           (throw t)))))))

(def ^:private inert-scalar-classes
  #{Long Double clojure.lang.BigInt clojure.lang.Ratio java.math.BigInteger
    java.math.BigDecimal Boolean String clojure.lang.Keyword clojure.lang.Symbol})

(defn inert-scalar?
  "Exact immutable scalar classes whose numeric operations cannot call host
  protocols. This is entry evidence, never a prediction from feedback."
  [x]
  (or (nil? x)
      (contains? inert-scalar-classes (class x))))

(defn- entry-env
  "The basis and mint the generic code of closure f runs under."
  [f env]
  (let [b (closure-basis f)]
    {:locals [] :basis (or b (:basis env)) :mint (or b (:mint env))}))

(defn call-value*
  "Apply value f to args: returns the next machine state."
  [f args env k]
  (cond
    (closure? f)
    (if-let [exe (enter-hook f [] args (or (closure-basis f) (:basis env)) k)]
      (run-executable exe args env k #(enter-closure f args env k) (entry-env f env))
      (enter-closure f args env k))

    (instance? Cont f)
    (if (some #(and (= :borrow (:tag %))
                    (not= :open (:status (a/state (:loan %))))) (:frames f))
      (raise (ex-info "klara: continuation outlived its lexical borrow" {:klara/error :authority}) env k)
    (if (= 1 (swap! (:shots f) inc))
      [:ret (first args) env (into k (rseq (:frames f)))]
      ;; fork-resume: a second resumption runs under a shot context
      (if-let [why (or (when (a/full-owned-held? (all-frames k))
                           "fork-resume: running context holds a full owned write share")
                         (resume-blocker (:frames f)))]
        (raise (ex-info (str "klara: " why) {:klara/error :authority}) env k)
        [:ret (first args) env (into (conj k (assoc (a/shot-frame) :env env)) (rseq (:frames f)))])))

    (pap? f)
    (if-let [exe (enter-hook (pap-fn f) (pap-statics f) args
                             (or (when (closure? (pap-fn f)) (closure-basis (pap-fn f)))
                                 (:basis env))
                             k)]
      (run-executable exe args env k
                      #(call-value* (pap-fn f) (into (vec (pap-statics f)) args) env k)
                      (if (closure? (pap-fn f)) (entry-env (pap-fn f) env) env))
      (call-value* (pap-fn f) (into (vec (pap-statics f)) args) env k))

    (instance? LocusRec f) (locus-rec-call f args env k)

    (ifn? f) (host-apply f args env k)

    :else (raise (ex-info "klara: not a function" {:value f}) env k)))

;; ---------------------------------------------------------------------------
;; the machine
;; ---------------------------------------------------------------------------

(defn- resolve-global [env sym k]
  (let [root (:basis env)
        e (w/entry root sym :value)]
    (cond
      (nil? e) (raise (ex-info (str "klara: unbound " sym) {:sym sym}) env k)
      (= :macro (:kind e)) (raise (ex-info (str "klara: macro as value " sym) {:sym sym}) env k)
      (w/pending? root e)
      (raise (ex-info (str "klara: " sym " is pending re-expansion in this basis")
                      {:sym sym :klara/error :pending
                       :invalid (w/invalid-reads root (:reads e))}) env k)
      :else [:ret (rebase (:value e) (:mint env)) env k])))

(defn- eval-list [node terms env k]
  (if (empty? terms)
    [:finish node [] env k]
    [:eval (first terms) env
     (conj k {:tag :list :node node :env env :vals [] :todo (rest terms)})]))

(defn- handle-keys [node] (sort (keys (:clauses node))))

(defn- list-terms
  "The subterms a node evaluates left to right before it finishes."
  [c]
  (case (:op c)
    (:app :specialize) (into [(:fn c)] (:args c))
    :prim (:args c)
    :perform (cond->> (:args c) (:target c) (into [(:target c)]))
    :handle (cond-> (mapv (:clauses c) (handle-keys c))
              (:return c) (conj (:return c)))))

(defn- finish [node vals env k]
  (case (:op node)
    :app (call-value* (first vals) (rest vals) env k)
    :prim (host-apply (core/prims (:name node)) vals env k)
    :perform (cond
               (:target node) (do-perform (first vals) (:name node) (rest vals) env k)
               (= "stage" (namespace (:name node))) (stage-perform (:name node) vals env k)
               (#{"auth" "own"} (namespace (:name node))) (auth-perform (:name node) vals env k)
               :else (binding [*outer-k* (conj *outer-k* k)]
                       (do-perform nil (:name node) vals env k)))
    :specialize [:ret (Pap. (first vals) (vec (rest vals))) env k]
    :handle (let [ks (handle-keys node)
                  clauses (zipmap ks vals)
                  ret (when (:return node) (nth vals (count ks)))
                  inst (->Instance (Object.) (:mode node))]
              [:eval (:body node) (push env inst)
               (conj k {:tag :handle :id (:id inst) :mode (:mode node) :env env
                        :clauses clauses :return ret})])))

(defn- step-eval [c env k]
  (case (:op c)
    :local   (let [v (lookup env (:index c))]
               ;; a binder of generated code seen from level 0 is its code
               [:ret (if (code/code-var? v) (code/->code (code/var-term (code/code-var-name v))) v)
                env k])
    :quote   [:ret (:datum c) env k]
    :fn      [:ret (Closure. c (:locals env) (:mint env)) env k]
    :resolve (resolve-global env (:id c) k)
    :let     [:eval (:init c) env (conj k {:tag :let :body (:body c) :env env})]
    :if      [:eval (:test c) env (conj k {:tag :if :node c :env env})]
    :letrec  (let [p (promise)
                   cs (mapv #(Closure. % (delay @p) (:mint env)) (:inits c))
                   ls (into (:locals env) cs)]
               (deliver p ls)
               [:eval (:body c) (assoc env :locals ls) k])
    (:app :prim :perform :specialize :handle) (eval-list c (list-terms c) env k)
    :code       (start-code c env k)
    :esc        (raise (ex-info "klara: esc outside code" {:klara/error :stage}) env k)))

(defn- step-ret [v k]
  (let [f (peek k) k (pop k)]
    (case (:tag f)
      :let (let [env (:env f)] [:eval (:body f) (push env v) k])
      :if (let [{:keys [node env]} f]
            [:eval (if v (:then node) (:else node)) env k])
      :list (let [vals (conj (:vals f) v)]
              (if-let [todo (seq (:todo f))]
                [:eval (first todo) (:env f) (conj k (assoc f :vals vals :todo (rest todo)))]
                [:finish (:node f) vals (:env f) k]))
      :borrow (do (unwind! f k) [:ret v (:env f) k])
      :capture-exit (do (cleanup-captured! (:frames f) k) [:ret v (:env f) k])
      :handle (if-let [r (:return f)]
                (call-value* r [v] (:env f) k)
                [:ret v nil k])
      :branch (if (= :shot (:mode (:ctx f)))
                (close-then-ret (:group (:ctx f)) v (:env f) k)
                [:ret v nil k])
      :fork-run (fork-continue f v k)
      :fork-scope (close-then-ret (:group f) v (:env f) k)
      :direct [:ret v nil k]
      :exe [:ret v nil k]
      (step-ret-stage f v k))))

;; ---------------------------------------------------------------------------
;; staging (S4): building code, splicing, run, lift, genlet, genletrec
;; ---------------------------------------------------------------------------
;;
;; (code e) evaluates by BUILDING e: the machine walks e's term at level
;; 1 in mode :build and returns an s-term (klara.code). A binder met at
;; level >= 1 gets a fresh name; its slot in the environment holds a
;; CodeVar marker, so a reference at level >= 1 emits the variable and a
;; reference from level 0 (inside esc) yields the variable's code. A
;; level-0 value referenced at level 1 is lifted implicitly (cross-stage
;; persistence, same rules as lift). (esc e) at level 1 evaluates e at
;; level 0 and splices the resulting code value.
;;
;; Build frames live on the continuation like every other frame:
;;   {:tag :blist ..}     a node whose children are being built; it
;;                        declares the fresh names of its binders
;;   {:tag :locus ..}     a let-insertion point: the top of every code
;;                        bracket and the body of every generated binder;
;;                        genlet adds bindings to it (an atom)
;;   {:tag :code-done}    wraps the finished s-term as a code value
;;   {:tag :splice ..}    receives the code value of a level-1 esc
;;   {:tag :wrap :op ..}  rebuilds a nested :code / :esc (levels > 1)
;;   {:tag :locus-rec ..} with-genletrec: memo table and letrec bindings
;;
;; A generated name is ALIVE while a frame declaring it is on the
;; continuation (or on a continuation suspended behind a host frame,
;; *outer-k*). This is BER MetaOCaml's dynamic scope-extrusion check:
;; splicing code that mentions a dead name, or running open code, is a
;; detected error rather than silently wrong code.

(defn- all-frames
  "Frames of the current continuation followed by those of the machines
  suspended behind host frames, innermost first."
  [k]
  (apply concat k *outer-k*))

(defn- frame-names [f]
  (case (:tag f)
    :blist (:names f)
    :locus (map first @(:bindings f))
    :locus-rec (vals (:table @(:state f)))
    nil))

(defn- alive-names [frames] (into #{} (mapcat frame-names) frames))

(defn- stage-error [msg & [kind data]]
  (ex-info msg (merge {:klara/error (or kind :stage)} data)))

(defn- check-alive
  "nil, or the extrusion error for the first free name of s-term t not
  alive in frames."
  [t frames what]
  (let [alive (alive-names frames)]
    (when-let [g (first (remove alive (code/free-vars t)))]
      (code/extrusion-error g what))))

(defn- new-locus [] {:tag :locus :bindings (atom [])})

(defn- start-code [c env k]
  [:build (:body c) (assoc env :level 1) (conj k {:tag :code-done} (new-locus))])

;; cross-stage persistence ----------------------------------------------------

(defn- plain-data? [v]
  (or (nil? v) (boolean? v) (number? v) (string? v) (keyword? v) (symbol? v) (char? v)))

(defn- host-fn-name [f]
  (let [n (clojure.main/demunge (.getName (class f)))]
    (clojure.string/replace n #"--\d+$" "")))

(declare lift-term)

(defn- resource-error [v]
  (stage-error (str "cannot lift a value holding a resource ("
                    (cond (instance? Instance v) "a handler instance"
                          (instance? Cont v) "a continuation"
                          (instance? LocusRec v) "a genletrec generator"
                          :else (.getSimpleName (class v)))
                    "); only data and functions over data persist into code")
               :lift {:value v}))

(defn- lift-closure [f seen]
  (code/core->s (closure-term f)
                (fn [i]
                  (let [ls (closure-locals f)
                        v (nth ls (- (count ls) 1 i))]
                    (when (code/code-var? v)
                      (throw (stage-error "cannot lift a closure that mentions a variable of generated code" :lift)))
                    (lift-term v seen)))))

(defn- scan-resources
  "Throw the lift error for the first resource reachable from v."
  [v seen]
  (cond
    (or (plain-data? v) (contains? seen v)) nil
    (record? v) (throw (resource-error v))
    (closure? v) (doseq [l (closure-locals v)] (scan-resources l (conj seen v)))
    (pap? v) (doseq [x (cons (pap-fn v) (pap-statics v))] (scan-resources x (conj seen v)))
    (coll? v) (doseq [x v] (scan-resources x seen))
    (code/code-var? v) nil
    (fn? v) nil
    :else (throw (resource-error v))))

(defn lift-term
  "The s-term that rebuilds present value v in generated code: data as a
  literal, closures as their code over lifted captures, partial
  applications as specialize, host functions and self-referential
  closures as opaque constants. Values holding resources (atoms, handler
  instances, continuations, other host objects) and code values are
  refused."
  ([v] (lift-term v #{}))
  ([v seen]
   (cond
     (code/code? v) (throw (stage-error "cannot lift a code value (splice it with esc instead)" :lift))
     (plain-data? v) {:op :quote :datum v}
     (record? v) (throw (resource-error v))
     (and (coll? v) (every? plain-data? (remove coll? (tree-seq coll? seq v)))
          (or (map? v) (vector? v) (set? v) (seq? v)))
     {:op :quote :datum v}
     (vector? v) {:op :prim :name 'vector :args (mapv #(lift-term % seen) v)}
     (set? v) {:op :prim :name 'hash-set :args (mapv #(lift-term % seen) v)}
     (map? v) {:op :prim :name 'hash-map :args (vec (mapcat (fn [[a b]] [(lift-term a seen) (lift-term b seen)]) v))}
     (seq? v) {:op :prim :name 'list :args (mapv #(lift-term % seen) v)}
     (closure? v)
     (if (contains? seen v)
       (throw (ex-info "cycle" {::cycle true}))
       (try (lift-closure v (conj seen v))
            (catch clojure.lang.ExceptionInfo e
              (if (::cycle (ex-data e))
                (do (scan-resources v #{}) {:op :quote :datum v :csp "fn"})
                (throw e)))))
     (pap? v) {:op :specialize :fn (lift-term (pap-fn v) seen)
               :args (mapv #(lift-term % seen) (pap-statics v))}
     (fn? v) {:op :quote :datum v :csp (host-fn-name v)}
     :else (throw (resource-error v)))))

(defn- csp [v env k]
  (try [:ret (lift-term v) nil k]
       (catch clojure.lang.ExceptionInfo e
         (raise (if (code/code? v)
                  (stage-error "a code value is used inside code without esc" :stage)
                  e)
                env k))))

;; building -------------------------------------------------------------------

(defn- next-child [fr k]
  (if-let [[child under?] (first (:todo fr))]
    (let [more (rest (:todo fr))
          fr' (assoc fr :todo more)
          env (if under? (:inner fr) (:outer fr))
          locus? (and under? (not (and (= :letrec (:op (:node fr))) (seq more))))]
      [:build child env (cond-> (conj k fr') locus? (conj (new-locus)))])
    [:ret (code/reassemble (:node fr) (:done fr) (:names fr)) nil k]))

(defn- step-build [c env k]
  (let [lvl (:level env)]
    (case (:op c)
      :local (let [v (lookup env (:index c))]
               (if (code/code-var? v)
                 [:ret (code/var-term (code/code-var-name v)) nil k]
                 (csp v env k)))
      (:quote :resolve) [:ret c nil k]
      :code [:build (:body c) (assoc env :level (inc lvl)) (conj k {:tag :wrap :op :code})]
      :esc (if (= 1 lvl)
             [:eval (:body c) (assoc env :level 0) (conj k {:tag :splice :env env})]
             [:build (:body c) (assoc env :level (dec lvl)) (conj k {:tag :wrap :op :esc})])
      (let [names (mapv code/fresh (code/binder-bases c (code/binder-arity c)))
            inner (reduce (fn [e nm] (push e (code/->code-var nm lvl))) env names)]
        (next-child {:tag :blist :node c :names names :outer env :inner inner
                     :done [] :todo (code/parts c)}
                    k)))))

(defn- wrap-bindings [bindings body]
  (reduce (fn [b [nm t]] {:op :let :names [nm] :init t :body b}) body (rseq bindings)))

(defn- find-locus-rec [frames id]
  (first (keep-indexed (fn [i f] (when (and (= :locus-rec (:tag f)) (= id (:id f))) [i f]))
                       frames)))

(defn- step-ret-stage [f v k]
  (case (:tag f)
    :blist (next-child (update f :done conj v) k)
    :locus [:ret (wrap-bindings @(:bindings f) v) nil k]
    :code-done [:ret (code/->code v) nil k]
    :wrap [:ret {:op (:op f) :body v} nil k]
    :splice (let [env (:env f)]
              (if-not (code/code? v)
                (raise (stage-error (str "esc expects a code value, got " (pr-str v))) env k)
                (let [t (code/code-term v)]
                  (if-let [e (check-alive t (all-frames k) "where it is spliced")]
                    (raise e env k)
                    [:ret t nil k]))))
    :locus-rec (let [{:keys [order bindings]} @(:state f)]
                 (cond
                   (not (code/code? v))
                   (raise (stage-error "with-genletrec: the body must produce code") (:env f) k)
                   (empty? order) [:ret v nil k]
                   :else [:ret (code/->code {:op :letrec :names order
                                             :inits (mapv bindings order)
                                             :body (code/code-term v)})
                          nil k]))
    :locus-rec-bind
    (let [env (:env f)
          frames (all-frames k)
          [i lf] (find-locus-rec frames (:id f))]
      (cond
        (not (and (code/code? v) (= :fn (:op (code/code-term v)))))
        (raise (stage-error "genletrec: the generator must produce the code of a fn") env k)
        (nil? lf) (raise (stage-error "genletrec: generator used outside its with-genletrec") env k)
        :else
        (if-let [e (check-alive (code/code-term v) (drop i frames)
                                "at the with-genletrec that binds it")]
          (raise e env k)
          (do (swap! (:state lf) assoc-in [:bindings (:name f)] (code/code-term v))
              [:ret (code/->code (code/var-term (:name f))) nil k]))))))

;; stage operations -----------------------------------------------------------

(defn- trivial-code? [t]
  (or (#{:var :resolve} (:op t))
      (and (= :quote (:op t)) (or (:csp t) (not (coll? (:datum t)))))))

(defn- genlet-target
  "Index (in frames) of the outermost locus that still has every name in
  fv in scope, or nil when there is no locus."
  [frames fv]
  (loop [fs (seq frames) i 0 target nil]
    (if-let [f (first fs)]
      (let [hit? (some (set fv) (frame-names f))]
        (case (:tag f)
          :locus (if hit? i (recur (next fs) (inc i) i))
          (:blist :locus-rec) (if hit? target (recur (next fs) (inc i) target))
          (recur (next fs) (inc i) target)))
      target)))

(defn- genlet [c env k]
  (if-not (code/code? c)
    (raise (stage-error (str "genlet expects a code value, got " (pr-str c))) env k)
    (let [t (code/code-term c)
          frames (all-frames k)]
      (if (trivial-code? t)
        [:ret c env k]
        (if-let [e (check-alive t frames "where genlet is called")]
          (raise e env k)
          (if-let [i (genlet-target frames (code/free-vars t))]
            (let [nm (code/fresh "t")]
              (swap! (:bindings (nth frames i)) conj [nm t])
              [:ret (code/->code (code/var-term nm)) env k])
            [:ret c env k]))))))

(defn- run-code [c env k]
  (if-not (code/code? c)
    (raise (stage-error (str "run expects a code value, got " (pr-str c))) env k)
    (let [t (try (code/s->core (code/code-term c)) (catch clojure.lang.ExceptionInfo e e))]
      (if (instance? Throwable t)
        (raise t env k)
        (if-let [es (seq (core/wf-errors t))]
          (raise (stage-error (str "run: ill-formed code: " (:error (first es)))) env k)
          [:eval t {:locals [] :basis (:basis env) :mint (:mint env)} k])))))

(def ^:private deopt-barrier-tags
  "Frames a deopt may not drop: they hold fork, capability or staging
  state that has no generic counterpart to rebuild (dropping a branch
  frame would leave its group open; rebuilding it would duplicate it)."
  #{:branch :fork-run :fork-scope :direct :blist :locus :code-done :splice :wrap
    :locus-rec :locus-rec-bind})

(defn- deopt-in-machine
  "(perform :stage/deopt i live) inside a speculative executable's Klara
  code: drop the residual's frames down to its marker, resume generic."
  [i live env k]
  (loop [kk k]
    (let [f (peek kk)]
      (cond
        (nil? f)
        (raise (stage-error "deopt! outside a speculative executable (or behind a host frame)") env k)
        (= :exe (:tag f)) (deopt-state (:exe f) i (vec live) env (pop kk))
        (deopt-barrier-tags (:tag f))
        (raise (stage-error (str "deopt! across a " (name (:tag f))
                                 " frame of the speculative code")) env k)
        :else (recur (pop kk))))))

;; frame states ---------------------------------------------------------------

(declare slot-val)

(defn- node-at [term path]
  (let [n (get-in term path)]
    (if (and (map? n) (:op n))
      n
      (throw (stage-error (str "frame state: no term at " (pr-str path)))))))

(defn- env-slots
  "The locals vector described by slots (outermost first). Slots may
  name earlier locals; [:letrec path i] slots of one group share a
  promise, as letrec's own closures do."
  [term slots live mint]
  (loop [ss (seq slots) ls [] groups {}]
    (if-not ss
      ls
      (let [[kind p i :as sl] (first ss)]
        (if (= :letrec kind)
          (let [cs (or (groups p)
                       (let [pr (promise)
                             cs (mapv #(Closure. % (delay @pr) mint) (:inits (node-at term p)))]
                         (deliver pr (into ls cs))
                         cs))]
            (recur (next ss) (conj ls (nth cs i)) (assoc groups p cs)))
          (recur (next ss) (conj ls (slot-val term sl live ls mint)) groups))))))

(defn- slot-val [term [kind a :as sl] live locals mint]
  (case kind
    :live (nth live a)
    :const a
    :local (nth locals a)
    :closure (Closure. (node-at term a) locals mint)
    :instance (->Instance (Object.) a)
    :vector (mapv #(slot-val term % live locals mint) a)
    (throw (stage-error (str "frame state: bad slot " (pr-str sl))))))

(defn- frame-of [term {:keys [tag path env] :as tpl} live locals envm]
  (let [term (or (:fn tpl) term)
        mint (:mint envm)
        fl (if (vector? env) (env-slots term env live mint) (subvec locals 0 env))
        fenv (assoc envm :locals fl)
        node (node-at term path)
        sv #(slot-val term % live fl mint)]
    (case tag
      :let {:tag :let :body (:body node) :env fenv}
      :if {:tag :if :node node :env fenv}
      :list (let [vals (mapv sv (:vals tpl))]
              {:tag :list :node node :env fenv :vals vals
               :todo (drop (inc (count vals)) (list-terms node))})
      :handle (let [inst (slot-val term (:instance tpl) live locals mint)]
                {:tag :handle :id (:id inst) :mode (:mode node) :env fenv
                 :clauses (update-vals (:clauses tpl) sv)
                 :return (some-> (:return tpl) sv)}))))

(defn materialize
  "The T0 machine state that frame state fs describes, for generic code
  term (a :fn term), live values live, over continuation k; env gives
  the basis and mint. A frame state is data:

    {:site s                       ; feedback site within the CodeId
     :at [:eval path]              ; resume by evaluating the term at path
       | [:ret slot]               ;   or by returning a value into :kont
     :env [slot ..]                ; the generic locals, outermost first:
                                   ;   captures, parameters, binders
     :kont [frame ..]}             ; generic frames, outermost first

  A slot is [:live j] (the j-th live value), [:const v], [:local j] (a
  local already rebuilt), and, for allocations the specialized code
  elided (virtual objects): [:closure path] (the fn at path over the
  locals so far), [:letrec path i] (the i-th closure of the letrec at
  path, its group sharing one environment), [:instance mode] (a fresh
  handler instance) and [:vector [slot ..]].

  A frame is {:tag t :path p :env n ..} with n the length of its
  environment (a prefix of :env) or a vector of slots (with :fn term,
  for an inlined caller's frame): :let and :if; :list (an :app, :prim,
  :perform, :handle or :specialize node with :vals [slot ..], the
  subterm values computed so far); :handle (:instance slot, :clauses
  {op slot}, :return slot), a handler the specialized code erased."
  [term fs live env k]
  (let [mint (:mint env)
        locals (env-slots term (:env fs) live mint)
        envm {:locals locals :basis (:basis env) :mint mint}
        k (reduce (fn [k tpl] (conj k (frame-of term tpl live locals envm))) k (:kont fs))
        [mode x] (:at fs)]
    (case mode
      :eval [:eval (node-at term x) envm k]
      :ret [:ret (slot-val term x live locals mint) envm k])))

(defn- stage-perform
  "Ambient stage operations. A dynamic handler for the operation wins (so
  generators can be instrumented); otherwise the reference meaning."
  [op args env k]
  (if (find-frame k #(and (= :dynamic (:mode %)) (contains? (:clauses %) op)))
    (do-perform nil op args env k)
    (let [[a] args]
      (case op
        :stage/run (run-code a env k)
        :stage/lift (try [:ret (code/->code (lift-term a)) env k]
                         (catch clojure.lang.ExceptionInfo e (raise e env k)))
        :stage/genlet (genlet a env k)
        :stage/deopt (deopt-in-machine a (second args) env k)
        :stage/locus-rec
        (let [lr (LocusRec. (Object.))
              fr {:tag :locus-rec :id (.-id lr) :env env
                  :state (atom {:table {} :order [] :bindings {}})}]
          (call-value* a [lr] env (conj k fr)))
        ;; Seed backends register additional stage operations through the same
        ;; reference-handler boundary as world operations. They remain effects
        ;; (dynamic handlers win), not additional core forms.
        (binding [*outer-k* (conj *outer-k* k)]
          (do-perform nil op args env k))))))

(defn- locus-rec-call
  "(g f key): the code of the function generated for key, generating it
  with (f key) the first time (BER MetaOCaml's mkgenlet)."
  [^LocusRec g args env k]
  (if-not (= 2 (count args))
    (raise (stage-error "a genletrec generator takes a generator fn and a key") env k)
    (let [[f key] args
          [_ lf] (find-locus-rec (all-frames k) (.-id g))]
      (if-not lf
        (raise (stage-error "genletrec generator used outside its with-genletrec"
                            :scope-extrusion) env k)
        (if-let [h (get-in @(:state lf) [:table key])]
          [:ret (code/->code (code/var-term h)) env k]
          (let [h (code/fresh "h")]
            (swap! (:state lf) #(-> % (assoc-in [:table key] h) (update :order conj h)))
            (call-value* f [key] env (conj k {:tag :locus-rec-bind :id (.-id g) :name h :env env}))))))))

;; ---------------------------------------------------------------------------
;; authority (S6): fork, adopt, direct, fork-resume admission
;; ---------------------------------------------------------------------------
;;
;; Frames:
;;   {:tag :fork-run ..}    collects branch values, starts the next branch
;;   {:tag :branch :ctx c}  a branch context (fork or shot); klara.authority
;;                          reads the chain of these from the continuation
;;   {:tag :fork-scope ..}  the body that sees the branches; returning
;;                          through it settles the group
;;   {:tag :direct ..}      irreversible effects run under a capability

(defn- close-then-ret [g v env k]
  (try (a/close-group! g (all-frames k) :exit)
       [:ret v env k]
       (catch clojure.lang.ExceptionInfo e (raise e env k))))

(defn- run-branch [g i vals thunks body-fn env k]
  (call-value* (nth thunks i) [] env
               (conj k
                     {:tag :fork-run :group g :i i :vals vals :thunks thunks :body-fn body-fn :env env}
                     {:tag :branch :ctx (a/group-ctx g i) :env env})))

(defn- fork-scope [g vals body-fn env k]
  (if body-fn
    (call-value* body-fn (a/branches g vals) env (conj k {:tag :fork-scope :group g :env env}))
    (close-then-ret g (vec vals) env k)))

(defn- fork-continue [f v k]
  (let [{:keys [group i vals thunks body-fn env]} f]
    (if-not (a/group-open? group)
      (raise (ex-info "klara: the fork has closed (a continuation captured in a branch was resumed after it)"
                      {:klara/error :authority})
             env k)
      (let [vals (conj vals v)
            i (inc i)]
        (if (< i (count thunks))
          (run-branch group i vals thunks body-fn env k)
          (fork-scope group vals body-fn env k))))))

(defn- auth-perform
  "Ambient authority operations. They are not handled by user handlers:
  an authority's state lives in the store, never in a handler."
  [op args env k]
  (try
    (let [frames (all-frames k)]
      (case op
        :own/borrow (let [[token body] args
                          loan (a/borrow-owned! token frames)]
                      (call-value* body [loan] env (conj k {:tag :borrow :loan loan :env env})))
        :auth/fork (let [[opts thunks body-fn] args
                         thunks (vec thunks)
                         g (a/open-fork! opts (count thunks) frames)]
                     (if (seq thunks)
                       (run-branch g 0 [] thunks body-fn env k)
                       (fork-scope g [] body-fn env k)))
        :auth/adopt [:ret (a/adopt! (first args)) env k]
        :auth/direct (let [[cap thunk] args
                           id (a/check-capability! cap frames)]
                       (call-value* thunk [] env (conj k {:tag :direct :cap cap :cap-id id :env env})))
        :auth/use (let [[r f & more] args]
                    (call-value* f (into [(a/op! :auth/payload [r] frames)] more) env k))
        [:ret (binding [*outer-k* (conj *outer-k* k)] (a/op! op args frames)) env k]))
    (catch Throwable e (raise e env k))))

(def ^:private skip-frame-keys
  #{:tag :node :body :todo :id :mode :names :outer :inner :done :state :bindings :ctx :group
    :cap-id :level :name :op :exe :code-id})

(defn- resume-blocker
  "nil if a continuation with these frames may be resumed again; else
  why not. Walks everything the frames hold: locals, collections and
  their metadata, closures' captures, partial applications, nested
  continuations, branch values. Lazy sequences and host objects (atoms)
  are not entered: an authority reached through them is checked when it
  is used, by the shot context."
  [frames]
  (let [seen (java.util.IdentityHashMap.)
        found (volatile! (when (a/full-owned-held? frames)
                           "fork-resume: context holds a full owned write share"))]
    (letfn [(walk [x]
              (when (and (nil? @found) (some? x) (not (plain-data? x)) (nil? (.put seen x true)))
                (cond
                  (a/auth? x) (vreset! found (a/resume-blocker x))
                  (closure? x) (run! walk (closure-locals x))
                  (pap? x) (do (walk (pap-fn x)) (run! walk (pap-statics x)))
                  (instance? Cont x) (run! frame (:frames x))
                  (a/branch? x) (walk (:value x))
                  (or (vector? x) (map? x) (set? x) (list? x))
                  (do (walk (meta x)) (run! walk x))
                  (instance? clojure.lang.IMeta x) (walk (meta x)))))
            (frame [f]
              (when (nil? @found)
                (case (:tag f)
                  :branch (when (and (= :fork (:mode (:ctx f))) (a/ctx-open? (:ctx f)))
                            (vreset! found "fork-resume: the continuation captured a running fork branch; it can be resumed only once"))
                  (:fork-run :fork-scope)
                  (when (a/group-open? (:group f))
                    (vreset! found "fork-resume: the continuation captured an open fork; it can be resumed only once"))
                  nil)
                (doseq [[kk vv] f :when (not (skip-frame-keys kk))]
                  (if (= :env kk) (some-> vv :locals walk) (walk vv)))))]
      (run! frame frames)
      @found)))

;; states: [:eval term env k] | [:build term env k] | [:ret value _ k]
;;         | [:finish node vals env k]
(defn step-state
  "One T0 transition; a terminal return state is unchanged. This low-level
   host interface does not isolate effects, settle frames, or meter host calls.
   A caller abandoning a state must establish that discarding its frames is
   permitted. The ordinary drive path retains its existing dispatch."
  [[mode c x k :as state]]
  (case mode
    :eval (step-eval c x k)
    :build (step-build c x k)
    :finish (finish c x (nth state 3) (nth state 4))
    :ret (if (empty? k) state (step-ret c k))))

(defn drive
  "Run the machine from state to a final value."
  [state]
  (loop [state state]
    (let [[mode c x k] state]
      (case mode
        :eval (recur (step-eval c x k))
        :build (recur (step-build c x k))
        :finish (let [[_ node vals env k] state] (recur (finish node vals env k)))
        :ret (if (empty? k) c (recur (step-ret c k)))))))

;; ---------------------------------------------------------------------------
;; entry points
;; ---------------------------------------------------------------------------

(defn run
  "Evaluate core term t. opts: :basis root (default: the fiber's pinned
  basis, else the empty root), :fiber, :mint (default = basis; nil for
  definition-time evaluation), :locals initial locals."
  ([t] (run t {}))
  ([t opts]
   (core/assert-wf! t)
   (let [basis (or (:basis opts) (some-> (:fiber opts) w/basis) *basis* w/empty-root)
         env {:locals (vec (:locals opts)) :basis basis
              :mint (if (contains? opts :mint) (:mint opts) basis)}]
     (binding [*fiber* (or (:fiber opts) *fiber*) *basis* basis]
       (drive [:eval t env '()])))))

(defn call-value
  "Host-side call of a Klara value. Compiled scalar regions pass explicit
  context; entries that can call arbitrary host code retain Var bindings."
  [f args]
  (let [b (or (when (closure? f) (closure-basis f)) *basis* w/empty-root)
        exe (when *direct-hook* (*direct-hook* f args b))]
    (if (and (:context-only? exe) (:invoke exe) *context-hook*
             (<= (count args) 4) (every? inert-scalar? args))
      (invoke-direct (*context-hook* b b *outer-k*) exe f args)
      (binding [*basis* b *mint* b]
        (if exe
          (invoke-direct exe f args)
          (drive (call-value* f args {:locals [] :basis b :mint b} '())))))))

;; ---------------------------------------------------------------------------
;; printing (the REPL and code printer rely on these)
;; ---------------------------------------------------------------------------

(defmethod print-method Closure [_ ^java.io.Writer w] (.write w "#<fn>"))
(defmethod print-method Pap [_ ^java.io.Writer w] (.write w "#<fn>"))
(defmethod print-method Instance [_ ^java.io.Writer w] (.write w "#<handler>"))
(defmethod print-method Cont [_ ^java.io.Writer w] (.write w "#<continuation>"))
(defmethod print-method LocusRec [_ ^java.io.Writer w] (.write w "#<genletrec>"))
