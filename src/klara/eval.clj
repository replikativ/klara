(ns klara.eval
  "T0: the reference interpreter of Klara Core K0 — the executable draft
  of the specification. Clarity over speed.

  A CEK machine. The state is [mode control env kont]:
    mode :eval  control is a term to evaluate,
    mode :ret   control is a value returning into kont.
  env is {:locals [v ..] :basis root :mint root|nil}; kont is a list of
  frames (top first). Every frame is plain data, so a captured
  continuation is a vector of frames and resuming it pushes them back:
  handlers are deep, resumption is multi-shot (T0 places no authority
  restriction on it yet). Calls in tail position push no frame, so self
  tail calls through letrec run in constant space (doc/01-core-v2 §1).

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
  guards hold; otherwise the generic path runs."
  (:require [klara.core :as core]
            [klara.world :as w]))

(def ^:dynamic *fiber* nil)
(def ^:dynamic *basis* nil)
(def ^:dynamic *entry-hook*
  "nil, or (fn [f statics args basis kont]) -> executable map or nil.
  kont is the caller's continuation (frames top first), so guards can
  inspect the handler context the call runs in."
  nil)

(defonce ^{:doc "Returned by a host executable (:run) to decline at entry: the
  generic path then runs from the start. Only sound for executables that
  performed no effect before declining (host executables perform none)."}
  deopt (Object.))

(declare call-value call-value*)

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

(defrecord Cont [frames])
(defrecord Instance [id mode])

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

(defn- host-apply [f args env k]
  (try [:ret (apply f args) env k]
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
                   (:version
                    (w/publish! (:world *fiber*)
                                #(w/put-entry % sym {:kind :def :value v :reads #{}
                                                     :code-id (str "value:" (System/identityHashCode v))
                                                     :value-id (str "value:" (System/identityHashCode v))}))))})

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

(defn- do-perform [target op args env k]
  (if target
    (if-let [[captured outer f] (and (instance? Instance target)
                                     (find-frame k #(= (:id target) (:id %))))]
      (if-let [cl (get (:clauses f) op)]
        (call-value* cl (conj (vec args) (->Cont captured)) env outer)
        (raise (ex-info (str "klara: instance does not handle " op) {:op op}) env k))
      (raise (ex-info (str "klara: unhandled lexical effect " op
                           " (instance out of extent, or behind a host frame)")
                      {:op op :klara/error :unhandled}) env k))
    (if-let [[captured outer f]
             (find-frame k #(and (= :dynamic (:mode %)) (contains? (:clauses %) op)))]
      (call-value* (get (:clauses f) op) (conj (vec args) (->Cont captured)) env outer)
      (if (= :exn/raise op)
        (let [ex (first args)]
          (throw (if (instance? Throwable ex)
                   ex
                   (ex-info "klara: uncaught exception" {:klara/exn ex}))))
        (if-let [h (reference-handlers op)]
          (try [:ret (h args env) env k]
               (catch Throwable t (raise t env k)))
          (raise (ex-info (str "klara: no handler for " op) {:op op}) env k))))))

;; ---------------------------------------------------------------------------
;; application
;; ---------------------------------------------------------------------------

(defn- enter-hook [f statics args basis k]
  (when *entry-hook* (*entry-hook* f statics args basis k)))

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

(defn- run-executable
  "An executable either names Klara code entered in THIS machine
  (:klara closure + :prefix arguments; effects keep working) or a host
  function (:run; a host frame, so it must not perform Klara effects).
  A host function may return `deopt`; then generic, a thunk producing the
  generic machine state, runs instead (replay from entry)."
  [exe args env k generic]
  (if-let [g (:klara exe)]
    (enter-closure g (into (vec (:prefix exe)) args) env k)
    (let [st (host-apply (:run exe) args env k)]
      (if (and (= :ret (nth st 0)) (identical? deopt (nth st 1)))
        (do (some-> (:deopts exe) (swap! inc)) (generic))
        st))))

(defn call-value*
  "Apply value f to args: returns the next machine state."
  [f args env k]
  (cond
    (closure? f)
    (if-let [exe (enter-hook f [] args (or (closure-basis f) (:basis env)) k)]
      (run-executable exe args env k #(enter-closure f args env k))
      (enter-closure f args env k))

    (instance? Cont f)
    [:ret (first args) env (into k (rseq (:frames f)))]

    (pap? f)
    (if-let [exe (enter-hook (pap-fn f) (pap-statics f) args
                             (or (when (closure? (pap-fn f)) (closure-basis (pap-fn f)))
                                 (:basis env))
                             k)]
      (run-executable exe args env k
                      #(call-value* (pap-fn f) (into (vec (pap-statics f)) args) env k))
      (call-value* (pap-fn f) (into (vec (pap-statics f)) args) env k))

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

(defn- finish [node vals env k]
  (case (:op node)
    :app (call-value* (first vals) (rest vals) env k)
    :prim (host-apply (core/prims (:name node)) vals env k)
    :perform (if (:target node)
               (do-perform (first vals) (:name node) (rest vals) env k)
               (do-perform nil (:name node) vals env k))
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
    :local   [:ret (lookup env (:index c)) env k]
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
    :app        (eval-list c (into [(:fn c)] (:args c)) env k)
    :prim       (eval-list c (:args c) env k)
    :perform    (eval-list c (cond->> (:args c) (:target c) (into [(:target c)])) env k)
    :specialize (eval-list c (into [(:fn c)] (:args c)) env k)
    :handle     (eval-list c (cond-> (mapv (:clauses c) (handle-keys c))
                               (:return c) (conj (:return c)))
                           env k)))

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
      :handle (if-let [r (:return f)]
                (call-value* r [v] (:env f) k)
                [:ret v nil k]))))

;; states: [:eval term env k] | [:ret value _ k] | [:finish node vals env k]
(defn drive
  "Run the machine from state to a final value."
  [state]
  (loop [state state]
    (let [[mode c x k] state]
      (case mode
        :eval (recur (step-eval c x k))
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
  "Host-side call of a Klara value (closures are IFn through this): a
  nested machine whose continuation stops at the host frame."
  [f args]
  (let [b (or (when (closure? f) (closure-basis f)) *basis* w/empty-root)]
    (binding [*basis* b]
      (drive (call-value* f args {:locals [] :basis b :mint b} '())))))

;; ---------------------------------------------------------------------------
;; printing (the REPL and code printer rely on these)
;; ---------------------------------------------------------------------------

(defmethod print-method Closure [_ ^java.io.Writer w] (.write w "#<fn>"))
(defmethod print-method Pap [_ ^java.io.Writer w] (.write w "#<fn>"))
(defmethod print-method Instance [_ ^java.io.Writer w] (.write w "#<handler>"))
(defmethod print-method Cont [_ ^java.io.Writer w] (.write w "#<continuation>"))
