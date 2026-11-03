(ns klara.runtime.machine
  "The reference semantics: a CEK machine (spec/L0-core.md#evaluation).

  A state is
    mode   :eval (ctl is a term, evaluated in env) or :ret (ctl is a value)
    k      the continuation: a stack of frames, top first (klara.runtime.stack,
           which also lists the frame kinds)
    world  the effective world E      (L1.context.*)
    mint   the basis stamped on new closures, nil or a world
    dyn    {:meter :defaults :session :job}: what belongs to the caller
           rather than to the code (budget, default handlers)

  Handlers are deep and continuations multi-shot (L3.handle.deep,
  L3.cont.multishot): a captured continuation is a vector of frames, and
  resuming it pushes them back. Calls in tail position push
  no frame (L0.eval.tail); closures capture only their :free locals
  (L0.space.closure).

  Intrinsics (runtime-provided guest functions that need the machine, see
  klara.lang.builtins) are called with the state and return a new state.

  Performance (STATUS.md#performance): the driver keeps its state in loop
  locals, evaluates immediate terms without frames, and builds a state map
  only on slow paths. Budgets count applications and loop iterations."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.prepare :as prep]
            [klara.runtime.stack :as ks]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Closure Continuation Code CodeVar World]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; Raised inside nested machines and compiled code to abandon them without
;; observable effects (L4.exec.leave): exhaustion and boundary-crossing effects.
(defrecord Abandon [reason])
(defn abandon! [reason] (throw (ex-info "abandon" {::abandon reason})))
(defn abandoned [^Throwable e] (when (instance? clojure.lang.ExceptionInfo e) (::abandon (ex-data e))))

;; Hooks set by later layers (L4): select a compiled implementation of a
;; definition, and call an executable.
;; Compiled code lives in the world (L4.exec.provenance), so a world's
;; resolution of a name never changes and caches are keyed by world id.
(defonce resolve-hook (atom nil))     ; (fn [q definition world] value-or-nil)

;; ---------------------------------------------------------------------------
;; Intrinsic values

;; Callable from host code (a host higher-order function given an intrinsic),
;; like closures (L3.effect.host-boundary).
(v/defrecord-callable Intrinsic [name f])

;; A letrec binding: siblings refer to each other through a cell that is
;; filled once all closures exist.
(deftype RecRef [^objects cell]
  clojure.lang.IDeref (deref [_] (aget cell 0))
  Object (toString [_] "#klara/rec"))
(defn- rec-ref [] (RecRef. (object-array 1)))
(defn- set-rec! [^RecRef r x] (aset ^objects (.-cell r) 0 x))

(defn intrinsic? [x] (instance? Intrinsic x))

(defn host-value
  "The value of a :host node: an intrinsic, a registered function, or the
   root of a clojure.core var."
  [q]
  (if-let [e (b/lookup q)]
    (case (:kind e)
      :intrinsic (->Intrinsic q (:fn e))
      :host (:fn e)
      (fail :L0.term.wf (str q " is not a value")))
    (let [v (resolve q)]
      (if (var? v) @v (fail :L1.resolve.unbound (str "unknown host function " q))))))

(def ^:private ^java.util.concurrent.ConcurrentHashMap host-cache (java.util.concurrent.ConcurrentHashMap.))

(defn- host-lookup [q]
  (or (.get host-cache q)
      (let [x (host-value q)] (.put host-cache q x) x)))

;; ---------------------------------------------------------------------------
;; Globals (L2.link.*)

(defn resolve-link
  "The value a link denotes in `world`: for a late link the definition's
   compiled code valid there (resolve-hook), else its value."
  [link ^World world]
  (case (:kind link)
    :late (let [q (:name link)
                d (w/lookup world q)]
            (when (nil? d) (fail :L1.resolve.unbound (str "unable to resolve " q " in " (w/id world)) :name q))
            (or (when-let [h @resolve-hook] (h q d world)) (:value d)))
    :pinned (w/pin (:world link) (:name link))
    :guarded (let [q (:name link)]
               (if (= (:generation link) (w/generation world q))
                 (:value link)
                 (resolve-link {:kind :late :name q} world)))))

;; ---------------------------------------------------------------------------
;; Closure application (on prepared nodes, klara.runtime.prepare)

(defn- select-arity
  "Index of the arity of closure `f` accepting `n` arguments (L0.eval.arity)."
  ^long [^Closure f ^long n]
  (let [^klara.runtime.prepare.Fn node (.-node f)
        as (.-arities node)
        cnt (count as)]
    (loop [i 0]
      (if (< i cnt)
        (let [^klara.runtime.prepare.Arity a (nth as i)]
          (if (and (not (.-rest? a)) (== n (.-nparams a))) i (recur (inc i))))
        (loop [i 0]
          (if (< i cnt)
            (let [^klara.runtime.prepare.Arity a (nth as i)]
              (if (and (.-rest? a) (>= n (.-nparams a))) i (recur (inc i))))
            (fail :L0.eval.arity (str "wrong number of arguments (" n ") passed to " f))))))))

(defn- owning
  "A vector owning array a (no copy for up to 32 elements)."
  [^objects a]
  (clojure.lang.LazilyPersistentVector/createOwning a))

(defn- prepend
  "[x] followed by the elements of vector v."
  [x v]
  (let [n (count v) a (object-array (inc n))]
    (aset a 0 x)
    (loop [i 0] (when (< i n) (aset a (inc i) (nth v i)) (recur (inc i))))
    (owning a)))

(defn- bind-args
  "The body environment: captured locals, the function itself if used, the
   parameters and (for a call) the rest argument as a seq, or (for recur) the
   rest argument as given."
  [^Closure f ^klara.runtime.prepare.Arity a args recur?]
  (let [env (.-env f)
        m (count env)
        self? (.-self? a)
        n (.-nparams a)
        rest? (.-rest? a)
        base (if self? (inc m) m)
        arr (object-array (cond-> (+ base n) rest? inc))]
    (loop [i 0] (when (< i m) (aset arr i (nth env i)) (recur (inc i))))
    (when self? (aset arr m f))
    (loop [i 0] (when (< i n) (aset arr (+ base i) (nth args i)) (recur (inc i))))
    (when rest?
      (aset arr (+ base n) (if recur? (nth args n) (seq (subvec (vec args) n)))))
    (owning arr)))

(defn prepare-term
  "Prepare a closed term for evaluation in an empty environment."
  [term]
  (prep/prep [] term host-lookup))

(defn closure-of
  "A closure for closed :fn `term` with basis `mint`."
  [term mint]
  (Closure. term (prep/prep-fn [] term host-lookup) [] mint))

;; ---------------------------------------------------------------------------
;; Code construction (L2.code.*)

(defn- splice-holes [term id bodies]
  (if (and (= :hole (:op term)) (= id (:code term)))
    (nth bodies (:index term))
    (t/with-children term (map #(splice-holes % id bodies) (t/children term)))))

(defn lift-term
  "The term embedding present value `x` (L2.lift.values, L2.lift.mutable)."
  [x]
  (when-let [m (v/find-mutable x)]
    (fail :L2.lift.mutable (str "cannot lift mutable " (type m) " into code") :value (str m)))
  (t/const x))

(def constructing
  "Fresh names bound by code constructions in progress on a stack
   (klara.runtime.stack/constructing)."
  ks/constructing)

(defn- instantiate
  "Finish a code node: holes have been evaluated to Code values. `allowed`
   are the fresh names of enclosing constructions in progress."
  [^klara.runtime.prepare.Code node env allowed tmpl hole-values]
  (let [term (.-term node)
        bodies (mapv (fn [c] (if (v/code? c) (.-term ^Code c)
                                 (fail :L2.esc.not-code (str "esc must produce code, got " (pr-str c)))))
                     hole-values)
        spliced (splice-holes tmpl (:id term) bodies)
        present (map (fn [[n slot]]
                       (let [x (nth env slot)]
                         [n (if (instance? RecRef x) @x x)]))
                     (.-free-slots node))
        ;; future-stage variables are renamed (a local, or the loop a recur
        ;; returns to); present values are lifted
        renaming (into {} (keep (fn [[n x]] (when (instance? CodeVar x) [n (:name x)]))) present)
        subst (into {} (keep (fn [[n x]] (when-not (instance? CodeVar x) [n (lift-term x)]))) present)
        result (t/refresh-free (t/substitute (t/rename spliced renaming) subst))
        allowed (into allowed (keep (fn [x] (when (instance? CodeVar x) (:name x)))) env)
        free (t/free-names result)
        extruded (remove allowed free)]
    (when (seq extruded)
      (fail :L2.code.extrusion
            (str "code refers to " (first extruded) " outside the code that binds it")
            :locals (vec extruded)))
    (Code. result)))

;; ---------------------------------------------------------------------------
;; The machine


(defn interop
  "Trusted host member access (L0 :interop)."
  [c vals]
  (let [[target args] (if (:static? c) [(:target c) vals] [(first vals) (rest vals)])
        args (object-array args)
        m (:member c)]
    (cond
      (:new? c) (clojure.lang.Reflector/invokeConstructor target args)
      (:static? c) (if (zero? (alength args))
                     (try (clojure.lang.Reflector/getStaticField ^Class target ^String m)
                          (catch Exception _ (clojure.lang.Reflector/invokeStaticMethod ^Class target ^String m args)))
                     (clojure.lang.Reflector/invokeStaticMethod ^Class target ^String m args))
      :else (if (zero? (alength args))
              (clojure.lang.Reflector/invokeNoArgInstanceMember target m false)
              (clojure.lang.Reflector/invokeInstanceMethod target m args)))))


;; ---------------------------------------------------------------------------
;; The current context for host code
;;
;; Host functions can call Klara closures back (clojure.core/map with a Klara
;; fn) and compiled code needs the effective world. Both read the context of
;; the innermost running machine from a thread-local holder: [world mint dyn].
;; The machine writes it before every host call; it is never a dynamic
;; binding, so host calls cost no binding push.

(def ^ThreadLocal context (ThreadLocal.))

(defn current-context
  "[world mint dyn] of the innermost running machine on this thread, or nil."
  []
  (.get context))

(defn set-context!
  "Set the context host code observes (compiled code, host callbacks).
   Returns the context array: a Klara callback that changes the world writes
   the new world back into it (see call-in)."
  ^objects [world mint dyn]
  (let [^objects h (.get context)] (aset h 0 world) (aset h 1 mint) (aset h 2 dyn) h))



(defn meter-of
  "The step meter of the context `c`, cached by the identity of its dyn."
  ^longs [^objects c]
  (let [dyn (aget c 2)]
    (if (identical? dyn (aget c 3))
      (aget c 4)
      (let [m (:meter dyn)] (aset c 3 dyn) (aset c 4 m) m))))

(defmacro ^:private with-context [world mint dyn & body]
  `(do (set-context! ~world ~mint ~dyn) ~@body))

;; ---------------------------------------------------------------------------
;; States for the slow paths
;;
;; The driver keeps its state in loop locals. Intrinsics, effects, exceptions
;; and jobs see a state map, the same shape as before:
;;   {:mode :eval|:ret|:apply|:done :ctl :env :k :world :mint :dyn}

(defn state [mode ctl env k world mint dyn]
  {:mode mode :ctl ctl :env env :k k :world world :mint mint :dyn dyn})

(defn perform
  "Perform `op` with `args` from state `st` (L3.perform.op)."
  [st op args]
  (let [k (:k st)
        i (ks/find-handler k op)
        a (when (>= i 0) (object-array (inc i)))
        below (when a (ks/split! k a (inc i)))
        frame (when a (aget a i))]
    (if (identical? :handle (ks/kind frame))
      (let [cont (Continuation. (owning a) (:world st) (:mint st))
            handler (get (:handlers frame) op)]
        ;; the handler runs outside its frame, in the handle expression's context
        (state :apply [handler (prepend cont args)] (:env st) below (:world frame) (:mint frame) (:dyn st)))
      ;; frame is nil or a stop frame
      (let [deopt (:deopt frame)]
        (if-let [d (and (not deopt) (get-in st [:dyn :defaults op]))]
          (d st args)
          (if deopt
            ;; L4.exec.leave: hand the whole state to the compiled caller
            (throw (ex-info "leave nested machine" {::abandon :effect ::state st}))
            (fail (if (identical? :boundary (ks/kind frame)) :L3.effect.host-boundary :L3.effect.unhandled)
                  (str "unhandled effect " op) :op op)))))))

;; The intrinsics klara.effect/perform and klara.effect/handle* (registered
;; in klara.runtime.intrinsics). step-apply recognizes them and runs the
;; common case on the registers (perform-op!, handle-op!); these are the rule.

(defn perform-intrinsic
  "(perform op & args), L3.perform.op."
  [st [op & args]]
  (when-not (keyword? op) (fail :L3.perform.op (str "operation must be a keyword, got " (pr-str op))))
  (perform st op (vec args)))

(defn handle-intrinsic
  "(handle* handlers thunk), L3.handle.deep: apply thunk under a handle frame."
  [st [handlers thunk]]
  (when-not (map? handlers) (fail :L3.handle.deep "handlers must be a map of operation to function"))
  (assoc st :mode :apply :ctl [thunk []]
         :k (ks/push (:k st) (ks/handle-frame (dissoc handlers :return) (:return handlers) (:world st) (:mint st)))))

;; ---------------------------------------------------------------------------
;; Klara stack traces (L0.trace.positions)

(def ^:private traced (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn- node-pos [x]
  (when (instance? klara.runtime.prepare.INode x)
    (:pos (.sourceTerm ^klara.runtime.prepare.INode x))))

(defn- frame-pos [f]
  (some node-pos (ks/frame-nodes f)))

(defn klara-trace
  "Source positions of the computation in state `st`, innermost first: the
   current node, then the frames of the continuation."
  [st]
  (->> (cons (node-pos (:ctl st)) (map frame-pos (:k st)))
       (remove nil?)
       dedupe
       vec))

(defn- attach-trace!
  "Prepend Klara frames to the host stack trace of `ex`, once."
  [^Throwable ex st]
  (when-not (.containsKey ^java.util.Map traced ex)
    (.put ^java.util.Map traced ex true)
    (let [elements (for [{:keys [line file in]} (klara-trace st)]
                     (StackTraceElement. "klara" (str (or in "top-level")) (if file (.getName (java.io.File. ^String file)) "REPL") (int (or line -1))))]
      (when (seq elements)
        (.setStackTrace ex (into-array StackTraceElement (concat elements (.getStackTrace ex)))))))
  ex)

(defn- raise
  "Unwind `st` with exception `ex` to the nearest try or job frame (L0.eval.exception)."
  [st ^Throwable ex]
  (attach-trace! ex st)
  (loop [k (:k st)]
    (if-let [f (first k)]
      (case (ks/kind f)
        :try (if-let [c (some #(when (instance? (:class %) ex) %) (:catches f))]
               (let [env (conj (:env f) ex)
                     k (if (:finally f) (ks/push (rest k) (ks/finally-ret-frame (:finally f) (:env f))) (rest k))]
                 (assoc st :mode :eval :ctl (:body c) :env env :k k :world (:world f) :mint (:mint f)))
               (if (:finally f)
                 (assoc st :mode :eval :ctl (:finally f) :env (:env f)
                        :k (ks/push (rest k) (ks/finally-throw-frame ex)) :world (:world f) :mint (:mint f))
                 (recur (rest k))))
        :job ((:on-throw f) (assoc st :k (rest k)) f ex)
        :boundary (throw ex)
        (recur (rest k)))
      (throw ex))))


(defn- exhaust
  "The budget ran out in `st` (L3.budget.exhausted). Inside a nested machine
   the host call is abandoned; the job that owns the budget then suspends
   at that call."
  [st]
  (let [stop (ks/stop-frame (:k st))]
    (cond
      (identical? :job (ks/kind stop)) ((get-in st [:dyn :on-exhausted]) st)
      ;; inside a nested machine of compiled code: leave with the state, so the
      ;; job suspends exactly here (L4.exec.leave)
      (:deopt stop) (throw (ex-info "leave nested machine" {::abandon :exhausted ::state st}))
      :else (abandon! :exhausted))))

(defn- job-snapshot [dyn] (when-let [j (:job dyn)] @j))

;; ---------------------------------------------------------------------------
;; Immediate nodes
;;
;; Constants, locals, globals, host values and closure creation never need a
;; continuation frame; neither do `flat` calls of host functions on immediate
;; arguments. Evaluating them inline is the main difference from a textbook
;; CEK machine; it changes no observable behaviour because none of them can
;; perform an effect or capture a continuation. Each is evaluated once.

(def ^:private none (Object.))

(defn- invoke-host [^clojure.lang.IFn f args]
  (case (count args)
    0 (.invoke f)
    1 (.invoke f (nth args 0))
    2 (.invoke f (nth args 0) (nth args 1))
    3 (.invoke f (nth args 0) (nth args 1) (nth args 2))
    4 (.invoke f (nth args 0) (nth args 1) (nth args 2) (nth args 3))
    5 (.invoke f (nth args 0) (nth args 1) (nth args 2) (nth args 3) (nth args 4))
    6 (.invoke f (nth args 0) (nth args 1) (nth args 2) (nth args 3) (nth args 4) (nth args 5))
    7 (.invoke f (nth args 0) (nth args 1) (nth args 2) (nth args 3) (nth args 4) (nth args 5) (nth args 6))
    8 (.invoke f (nth args 0) (nth args 1) (nth args 2) (nth args 3) (nth args 4) (nth args 5) (nth args 6) (nth args 7))
    (apply f args)))

(defn- resolve-global [^klara.runtime.prepare.Global g world dyn]
  (let [link (.-link g)]
    (if (= :late (:kind link))
      (let [id (.-id ^World world)]
        (or (prep/global-cached g id)
            (prep/global-cache! g id (resolve-link link world))))
      (resolve-link link world))))

(declare imm)

(defn- imm-all
  "Evaluate argument nodes known to be immediate (prep/imm-node?)."
  [args env world mint dyn ctx]
  (case (count args)
    0 []
    1 [(imm (nth args 0) env world mint dyn ctx)]
    2 (let [a (imm (nth args 0) env world mint dyn ctx)] [a (imm (nth args 1) env world mint dyn ctx)])
    3 (let [a (imm (nth args 0) env world mint dyn ctx) b (imm (nth args 1) env world mint dyn ctx)]
        [a b (imm (nth args 2) env world mint dyn ctx)])
    (let [n (count args) a (object-array n)]
      (loop [i 0] (when (< i n) (aset a i (imm (nth args i) env world mint dyn ctx)) (recur (inc i))))
      (owning a))))

(defn- imm-prefix
  "Evaluate the leading immediate argument nodes of vector `args`. Returns
   [values remaining], where `remaining` is the vector of nodes from the first
   non-immediate one (or nil)."
  [args env world mint dyn ctx]
  (let [args (if (vector? args) args (vec args))
        n (count args) a (object-array n)]
    (loop [i 0]
      (if (== i n)
        [(owning a) nil]
        (let [x (imm (nth args i) env world mint dyn ctx)]
          (if (identical? x none)
            [(owning (java.util.Arrays/copyOf a i)) (subvec args i)]
            (do (aset a i x) (recur (inc i)))))))))

(defn- imm
  "The value of node `c` if it is immediate, else `none`. `ctx` is the running
   machine's context array (see run-state), which a flat host call publishes:
   a lazy sequence it realizes may call Klara code back."
  [c env world mint dyn ^objects ctx]
  ;; class tests, most frequent first: cheaper than the interface call of
  ;; prep/tag on this, the hottest dispatch of the interpreter
  (cond
    (instance? klara.runtime.prepare.Local c)
    (let [x (.nth ^clojure.lang.Indexed env (.-slot ^klara.runtime.prepare.Local c))]
      (if (instance? RecRef x) @x x))
    (instance? klara.runtime.prepare.Const c) (.-value ^klara.runtime.prepare.Const c)
    (instance? klara.runtime.prepare.App c)
    (let [^klara.runtime.prepare.App c c]
      (if (.-flat c)
        (let [hf (.-value ^klara.runtime.prepare.Host (.-f c))
              vals (imm-all (.-args c) env world mint dyn ctx)]
          (when-not (instance? clojure.lang.IFn hf)
            (fail :L0.eval.not-fn (str "cannot call " (pr-str hf) ": not a function")))
          (aset ctx 0 world) (aset ctx 1 mint) (aset ctx 2 dyn)
          (invoke-host hf vals))
        none))
    (instance? klara.runtime.prepare.Global c) (resolve-global c world dyn)
    (instance? klara.runtime.prepare.Host c) (.-value ^klara.runtime.prepare.Host c)
    (instance? klara.runtime.prepare.Fn c)
    (let [^klara.runtime.prepare.Fn c c
          cap (.-captured c)]
      (Closure. (.-term c) c (case (count cap)
                               0 []
                               1 [(nth env (nth cap 0))]
                               2 [(nth env (nth cap 0)) (nth env (nth cap 1))]
                               (mapv #(nth env %) cap))
                mint))
    :else none))

;; ---------------------------------------------------------------------------
;; The driver

(defn- charge!
  "One step per application and loop iteration (L3.budget.steps). True when
   the budget is exhausted."
  [meter]
  (when meter
    (let [^longs m meter n (dec (aget m 0))]
      (aset m 0 n)
      (neg? n))))

(defn- profiling? [dyn] (nil? (:no-profile dyn)))

;; What the steps need from dyn, cached in the registers by its identity (dyn
;; changes only where a job, a handler context or klara.profile/without
;; switches it): register 8 the dyn they were read from, 9 its step meter,
;; 10 whether profiles are recorded (L4.profile.record).
(defn- sync-dyn! [^objects regs dyn]
  (when-not (identical? dyn (aget regs 8))
    (aset regs 8 dyn) (aset regs 9 (:meter dyn)) (aset regs 10 (profiling? dyn))))

(defn- self-call-frame?
  "Is args frame f completing a definition's call of itself?"
  [f]
  (let [n (:node f)]
    (and (instance? klara.runtime.prepare.App n) (.-self-call ^klara.runtime.prepare.App n))))

(defn- record-entry!
  "L4.profile.record: a function entry (or loop iteration) with its arguments."
  [prof ^Closure f args external]
  (when prof
    (.enter ^klara.runtime.prepare.IProfile (.-profile ^klara.runtime.prepare.Fn (.-node f)) args (boolean external))))

(defn- record-call! [prof ^klara.runtime.prepare.App c fv]
  (when (and prof (or (instance? Closure fv) (instance? klara.runtime.value.IExecutable fv)))
    (.call ^klara.runtime.prepare.IProfile (.-profile c) fv)))

(defn- record-branch! [prof ^klara.runtime.prepare.If c x]
  (when prof (.branch ^klara.runtime.prepare.IProfile (.-profile c) (boolean x))))

(defn- save! [^objects r mode ctl env k world mint dyn]
  (aset r 0 mode) (aset r 1 ctl) (aset r 2 env) (aset r 3 k)
  (aset r 4 world) (aset r 5 mint) (aset r 6 dyn))

(defn- regs-state [^objects r] (state (aget r 0) (aget r 1) (aget r 2) (aget r 3) (aget r 4) (aget r 5) (aget r 6)))

;; Each step reads the state from the register array `regs`, and either
;; writes the next state there and returns nil (the fast path), or returns a
;; state map for a slow path. Steps are separate functions so that each stays
;; small enough for the JVM to compile.

(defn- next!
  "Continue on the fast path with this state."
  [^objects regs mode ctl env k world mint dyn]
  (save! regs mode ctl env k world mint dyn)
  nil)

(defn- step-eval [regs]
  (let [^objects regs regs
        mode (aget regs 0) ctl (aget regs 1) env (aget regs 2) k (aget regs 3)
        world (aget regs 4) mint (aget regs 5) dyn (aget regs 6) ctx (aget regs 7)
        _ (sync-dyn! regs dyn)
        meter (aget regs 9) prof (aget regs 10)]
      (let [c ctl
            x (imm c env world mint dyn ctx)]
        (if-not (identical? x none)
          (next! regs :ret x env k world mint dyn)
          (case (prep/tag c)
            5 (let [^klara.runtime.prepare.App c c
                    fv (imm (.-f c) env world mint dyn ctx)
                    _ (when-not (identical? fv none) (record-call! prof c fv))]
                (cond
                  (identical? fv none)
                  (next! regs :eval (.-f c) env (ks/push k (ks/args-frame c (.-args c) [] env (.-recur-arity c))) world mint dyn)
                  (and (.-all-imm c) (instance? Closure fv) (nil? (.-basis ^Closure fv)) (not (charge! meter)))
                  ;; the common case: an open closure on immediate arguments, entered directly
                  (let [^Closure fv fv
                        args (imm-all (.-args c) env world mint dyn ctx)
                        ra (.-recur-arity c)
                        i (if ra (long ra) (select-arity fv (count args)))
                        ^klara.runtime.prepare.Arity a (nth (.-arities ^klara.runtime.prepare.Fn (.-node fv)) i)]
                    (record-entry! prof fv args (not (.-self-call c)))
                    (next! regs :eval (.-body a) (bind-args fv a args (boolean ra)) k world mint dyn))
                  (.-all-imm c)
                  (next! regs :apply [fv (imm-all (.-args c) env world mint dyn ctx) (.-recur-arity c) (.-self-call c)] env k world mint dyn)
                  :else
                  (let [[vals remaining] (imm-prefix (.-args c) env world mint dyn ctx)]
                    (if (nil? remaining)
                      (next! regs :apply [fv vals (.-recur-arity c) (.-self-call c)] env k world mint dyn)
                      (next! regs :eval (first remaining) env
                             (ks/push k (ks/args-frame c (subvec remaining 1) (prepend fv vals) env (.-recur-arity c)))
                             world mint dyn)))))
            6 (let [^klara.runtime.prepare.Let c c
                    x (imm (.-init c) env world mint dyn ctx)]
                (if (identical? x none)
                  (next! regs :eval (.-init c) env (ks/push k (ks/let-frame (.-body c) env)) world mint dyn)
                  (next! regs :eval (.-body c) (conj env x) k world mint dyn)))
            8 (let [^klara.runtime.prepare.If c c
                    x (imm (.-test c) env world mint dyn ctx)]
                (if (identical? x none)
                  (next! regs :eval (.-test c) env (ks/push k (ks/if-frame c (.-then c) (.-else c) env)) world mint dyn)
                  (do (record-branch! prof c x)
                      (next! regs :eval (if x (.-then c) (.-else c)) env k world mint dyn))))
            9 (let [^klara.runtime.prepare.Do c c
                    exprs (.-exprs c)]
                (if (seq exprs)
                  (next! regs :eval (first exprs) env (ks/push k (ks/do-frame (concat (rest exprs) [(.-last c)]) env)) world mint dyn)
                  (next! regs :eval (.-last c) env k world mint dyn)))
            7 (let [^klara.runtime.prepare.Letrec c c
                    fns (.-fns c)
                    refs (mapv (fn [_] (rec-ref)) fns)
                    env' (into env refs)]
                (doseq [[r ^klara.runtime.prepare.Fn f] (map vector refs fns)]
                  (set-rec! r (Closure. (.-term f) f (mapv #(nth env' %) (.-captured f)) mint)))
                (next! regs :eval (.-body c) env' k world mint dyn))
            10 (let [^klara.runtime.prepare.Recur c c
                     self (let [x (nth env (.-slot c))] (if (instance? RecRef x) @x x))
                     fast (and (.-all-imm c) (nil? (.-basis ^Closure self)))
                     osr (when fast (.osr ^klara.runtime.prepare.IOsr (.-node ^Closure self)))
                     compiled (when osr (osr self world mint))]
                 (cond
                   ;; L4.exec.osr: compiled code for this loop exists and holds here;
                   ;; its entry charges this iteration's step (L4.lower.steps)
                   compiled
                   (next! regs :apply [compiled (imm-all (.-args c) env world mint dyn ctx) nil] env k world mint dyn)
                   (and fast (not (charge! meter)))
                   ;; a loop iteration: re-enter the arity directly (L0.eval.tail)
                   (let [^Closure self self
                         fnode (.-node self)
                         ^klara.runtime.prepare.Arity a (nth (.-arities ^klara.runtime.prepare.Fn fnode) (.-arity c))
                         args (imm-all (.-args c) env world mint dyn ctx)]
                     (record-entry! prof self args true)
                     (next! regs :eval (.-body a) (bind-args self a args true) k world mint dyn))
                   :else
                 (let [[vals remaining] (if (.-all-imm c)
                                        [(imm-all (.-args c) env world mint dyn ctx) nil]
                                        (imm-prefix (.-args c) env world mint dyn ctx))]
                 (if (nil? remaining)
                   (next! regs :apply [self vals (.-arity c)] env k world mint dyn)
                   (next! regs :eval (first remaining) env
                          (ks/push k (ks/args-frame c (subvec remaining 1) (prepend self vals) env (.-arity c)))
                          world mint dyn)))))
            11 (next! regs :eval (.-ex ^klara.runtime.prepare.Throw c) env (ks/push k ks/throw-frame) world mint dyn)
            12 (let [^klara.runtime.prepare.Try c c]
                 (next! regs :eval (.-body c) env
                        (ks/push k (ks/try-frame (.-catches c) (.-finally c) env world mint))
                        world mint dyn))
            13 (let [^klara.runtime.prepare.Interop c c
                     cs (.-args c)]
                 (if (seq cs)
                   (next! regs :eval (first cs) env (ks/push k (ks/interop-frame (.-term c) (rest cs) [] env)) world mint dyn)
                   (next! regs :ret (do (set-context! world mint dyn) (interop (.-term c) [])) env k world mint dyn)))
            14 (let [^klara.runtime.prepare.Def c c]
                 (when mint (fail :L1.def.pinned (str "def of " (:name (.-term c)) " in a pinned context")))
                 (next! regs :eval (.-init c) env (ks/push k (ks/def-frame (.-term c))) world mint dyn))
            15 (let [^klara.runtime.prepare.Code c c
                     term (.-term c)
                     [tmpl renaming] (t/freshen (:template term))
                     hole-env (into env (map (fn [b] (v/->CodeVar (get renaming b b)))) (.-binders c))
                     holes (.-holes c)]
                 (if (seq holes)
                   (next! regs :eval (first holes) hole-env
                          (ks/push k (ks/code-frame c env hole-env tmpl (into (constructing k) (vals renaming))
                                                    (rest holes) []))
                          world mint dyn)
                   (next! regs :ret (instantiate c env (constructing k) tmpl []) env k world mint dyn)))
            (fail :L0.term.wf (str "unknown node " c)))))))

(defn- step-ret [regs]
  (let [^objects regs regs
        mode (aget regs 0) ctl (aget regs 1) env (aget regs 2) k (aget regs 3)
        world (aget regs 4) mint (aget regs 5) dyn (aget regs 6) ctx (aget regs 7)
        _ (sync-dyn! regs dyn)
        meter (aget regs 9) prof (aget regs 10)]
      (if (empty? k)
        (state :done ctl env k world mint dyn)
        (let [x ctl f (first k) k (rest k)]
          (case (ks/kind f)
            :args (let [vals (conj (:vals f) x)]
                    (if-let [todo (not-empty (:todo f))]
                      (let [[more remaining] (imm-prefix todo (:env f) world mint dyn ctx)
                            vals (reduce conj vals more)]
                        (if (nil? remaining)
                          (next! regs :apply [(first vals) (subvec vals 1) (:recur f) (self-call-frame? f)] env k world mint dyn)
                          (next! regs :eval (first remaining) (:env f)
                                 (ks/push k (ks/args-frame (:node f) (subvec remaining 1) vals (:env f) (:recur f))) world mint dyn)))
                      (next! regs :apply [(first vals) (subvec vals 1) (:recur f) (self-call-frame? f)] env k world mint dyn)))
            :let (next! regs :eval (:body f) (conj (:env f) x) k world mint dyn)
            :if (do (record-branch! prof (:node f) x)
                    (next! regs :eval (if x (:then f) (:else f)) (:env f) k world mint dyn))
            :do (let [[a & more] (:rest f)]
                  (next! regs :eval a (:env f) (if more (ks/push k (ks/do-frame more (:env f))) k) world mint dyn))
            :restore (next! regs :ret x env k (:world f) (:mint f) dyn)
            :restore-profile (next! regs :ret x env k world mint
                                    (if (:no-profile f) (assoc dyn :no-profile true) (dissoc dyn :no-profile)))
            :binders (next! regs :ret x env k world mint dyn)
            :handle (if-let [r (:return f)]
                      (next! regs :apply [r [x]] env k (:world f) (:mint f) dyn)
                      (next! regs :ret x env k world mint dyn))
            :try (if (:finally f)
                   (next! regs :eval (:finally f) (:env f) (ks/push k (ks/finally-value-frame x)) world mint dyn)
                   (next! regs :ret x env k world mint dyn))
            :finally-value (next! regs :ret (:value f) env k world mint dyn)
            :finally-ret (next! regs :eval (:term f) (:env f) (ks/push k (ks/finally-value-frame x)) world mint dyn)
            :finally-throw (raise (state :ret x env k world mint dyn) (:ex f))
            :throw (raise (state :ret x env k world mint dyn)
                          (if (instance? Throwable x) x
                              (ex-info (str "throw of a non-throwable: " (pr-str x)) {:rule :L0.eval.exception :value x})))
            :interop (let [vals (conj (:vals f) x)]
                       (if-let [[a & more] (seq (:todo f))]
                         (next! regs :eval a (:env f) (ks/push k (ks/interop-frame (:term f) more vals (:env f))) world mint dyn)
                         (next! regs :ret (do (set-context! world mint dyn) (interop (:term f) vals)) env k world mint dyn)))
            :def (let [c (:term f)]
                   (perform (state :ret x env k world mint dyn) :world/define
                            [(:name c) {:form (:form c) :term (:init c) :value x :macro? (:macro? c) :meta (:meta c)}]))
            :code (let [vals (conj (:vals f) x)]
                    (if-let [[a & more] (seq (:todo f))]
                      (next! regs :eval a (:hole-env f)
                             (ks/push k (ks/code-frame (:node f) (:env f) (:hole-env f) (:tmpl f) (:bound f) more vals))
                             world mint dyn)
                      (next! regs :ret (instantiate (:node f) (:env f) (constructing k) (:tmpl f) vals) env k world mint dyn)))
            :job ((:on-return f) (state :ret x env k world mint dyn) f x)
            :boundary (state :done x env k world mint dyn)
            :frame-fn ((:fn f) (state :ret x env k world mint dyn) x))))))

(defonce ^{:doc "Take resume-in-place where it applies. Off, every effect
  takes the rule as written; the suites run both ways."}
  tail-resume? (atom true))

(defn- resume-in-place?
  "Can clause `h`, applied to `n` arguments, resume in place?"
  [h ^long n meter]
  (and (instance? Closure h) (nil? (.-basis ^Closure h))
       (some? (.-tail-arg ^klara.runtime.prepare.Fn (.-node ^Closure h)))
       (== n (.-nparams ^klara.runtime.prepare.Arity (nth (.-arities ^klara.runtime.prepare.Fn (.-node ^Closure h)) 0)))
       (or (nil? meter) (>= (aget ^longs meter 0) 2))
       @tail-resume?))

(defn- resume-in-place!
  "The clause application `h` to `args` (the first the continuation `cont`
   of the stack `k` above `below`), when `h` is (fn [k ..] (k e)) and e is
   immediate (klara.runtime.prepare/tail-arg). The rule applies the clause on
   `below`, in the handle's world and mint `fworld` `fmint`; its body applies
   cont to the value of e in tail position, which pushes the frames of cont
   back onto `below`, giving `k`, in the perform's world and mint. That is two
   applications, so two steps (L3.budget.steps), and resume-in-place? asks for
   both to be there: otherwise the rule runs, and exhausts where it does. e
   cannot perform, leave or call Klara code (it is immediate), so nothing
   else can happen in between. What is observable is kept: the clause's
   profile records its entry with the real continuation (L4.profile.record),
   and while e is evaluated the registers hold the state the rule would be
   in, so an exception e raises is raised from there (L0.eval.exception,
   L0.trace.positions)."
  [^objects regs ^Closure h args k below world mint fworld fmint dyn]
  (let [meter (aget regs 9)
        ^klara.runtime.prepare.Fn node (.-node h)
        ^klara.runtime.prepare.Arity a (nth (.-arities node) 0)
        _ (charge! meter)
        _ (record-entry! (aget regs 10) h args true)
        env' (bind-args h a args false)]
    (save! regs :eval (.-body a) env' below fworld fmint dyn)
    (let [v (imm (.-tail-arg node) env' fworld fmint dyn (aget regs 7))]
      (charge! meter)
      (next! regs :ret v nil k world mint dyn))))

(defn- perform-op!
  "perform-intrinsic on the registers, for the common case: a keyword
   operation with a handler on the stack. The clause application is the
   state perform returns (L3.perform.op); any other case takes perform."
  [^objects regs ctl args env k world mint dyn]
  (let [op (when (pos? (count args)) (nth args 0))
        i (if (keyword? op) (ks/find-handler k op) -1)
        a (when (>= i 0) (object-array (inc i)))
        below (when a (ks/split! k a (inc i)))
        frame (when a (aget a i))]
    (if (identical? :handle (ks/kind frame))
      (let [h (get (:handlers frame) op)
            ;; [op & args] becomes [continuation & args]
            args (assoc (if (vector? args) args (vec args)) 0 (Continuation. (owning a) world mint))]
        (if (resume-in-place? h (count args) (aget regs 9))
          (resume-in-place! regs h args k below world mint (:world frame) (:mint frame) dyn)
          (next! regs :apply [h args] env below (:world frame) (:mint frame) dyn)))
      (perform-intrinsic (state :apply ctl env k world mint dyn) args))))

(defn- handle-op!
  "handle-intrinsic on the registers, for well-formed arguments."
  [^objects regs ctl args env k world mint dyn]
  (let [handlers (when (== 2 (count args)) (nth args 0))]
    (if (map? handlers)
      (next! regs :apply [(nth args 1) []] env
             (ks/push k (ks/handle-frame (dissoc handlers :return) (:return handlers) world mint)) world mint dyn)
      (handle-intrinsic (state :apply ctl env k world mint dyn) args))))

(defn- step-apply [regs]
  (let [^objects regs regs
        mode (aget regs 0) ctl (aget regs 1) env (aget regs 2) k (aget regs 3)
        world (aget regs 4) mint (aget regs 5) dyn (aget regs 6)
        _ (sync-dyn! regs dyn)
        meter (aget regs 9) prof (aget regs 10)]
      (let [[fv args recur-arity] ctl]
        (cond
          (instance? Closure fv)
          (if (charge! meter)
            (exhaust (state :apply ctl env k world mint dyn))
            (let [^Closure fv fv
                  i (if recur-arity (long recur-arity) (select-arity fv (count args)))
                  ^klara.runtime.prepare.Arity a (nth (.-arities ^klara.runtime.prepare.Fn (.-node fv)) i)
                  _ (record-entry! prof fv args (not (get ctl 3)))
                  env' (bind-args fv a args (boolean recur-arity))
                  basis (.-basis fv)]
              (if (and basis (not (identical? basis mint)))
                ;; L1.context.call-based: run in the basis, restore afterwards
                (next! regs :eval (.-body a) env'
                       (if (identical? :restore (ks/kind (first k))) k (ks/push k (ks/restore-frame world mint)))
                       basis basis dyn)
                (next! regs :eval (.-body a) env' k world mint dyn))))

          (instance? Continuation fv)
          (let [^Continuation fv fv]
            (when-not (= 1 (count args)) (fail :L0.eval.arity "a continuation takes one argument"))
            (if (charge! meter)
              (exhaust (state :apply ctl env k world mint dyn))
              (next! regs :ret (first args) nil (ks/reinstate k (.-frames fv)) (.-world fv) (.-mint fv) dyn)))

          (instance? Intrinsic fv)
          (let [g (.-f ^Intrinsic fv)]
            (cond
              (identical? g perform-intrinsic) (perform-op! regs ctl args env k world mint dyn)
              (identical? g handle-intrinsic) (handle-op! regs ctl args env k world mint dyn)
              :else (g (state :apply ctl env k world mint dyn) args)))

          (instance? klara.runtime.value.IExecutable fv)
          (v/-execute fv (state :apply ctl env k world mint dyn) args)

          (not (instance? clojure.lang.IFn fv))
          (fail :L0.eval.not-fn (str "cannot call " (pr-str fv) ": not a function") :value (pr-str fv))

          :else
          (let [snapshot (job-snapshot dyn)
                ctx (doto (set-context! world mint dyn)
                      ;; callbacks see the construction they are part of (constructing)
                      (aset 5 k))
                r (try (invoke-host fv args)
                       (catch Throwable ex
                         (when (abandoned ex)
                           ;; nothing the abandoned host call did may survive (L4.exec.leave)
                           (when snapshot (reset! (:job dyn) snapshot))
                           (throw ex))
                         (reduced ex)))]
            (if (reduced? r)
              (raise (state :apply ctl env k world mint dyn) @r)
              ;; a callback may have changed the world (read-your-writes across
              ;; host code, L1.def.read-your-writes)
              (next! regs :ret r nil k (aget ctx 0) mint dyn)))))))

(defn- drive
  "The fast path: run steps until one returns a state map (a slow path:
   intrinsic, effect, exception, job, done). `regs` always holds the state of
   the current step, for the exception handler."
  [st ^objects regs]
  (save! regs (:mode st) (:ctl st) (:env st) (:k st) (:world st) (:mint st) (:dyn st))
  (loop []
    (let [mode (aget regs 0)
          ;; identity tests: the modes are constants, and case would hash them
          r (cond
              (identical? mode :eval) (step-eval regs)
              (identical? mode :ret) (step-ret regs)
              (identical? mode :apply) (step-apply regs)
              :else (regs-state regs))]
      (if (nil? r) (recur) r))))

(defn run-state
  "Run state map `st` until it returns from its last frame. Returns the final
   state map."
  [st]
  (let [saved (.get context)
        regs (object-array 11)
        ctx (object-array 6)]
    ;; world mint dyn, the meter cached per dyn (see meter-of), and the
    ;; continuation of the host call in progress (see constructing)
    (.set context ctx)
    (aset regs 7 ctx)
    (aset regs 8 none)
    (try
      (loop [st st]
        (let [r (try (drive st regs)
                     (catch Throwable ex
                       (let [st (regs-state regs)]
                         (if-let [reason (abandoned ex)]
                           (if (and (= reason :exhausted) (identical? :job (ks/kind (ks/stop-frame (:k st)))))
                             ;; the budget ran out inside a host call: the host's stack
                             ;; is gone, and running the call again would repeat what
                             ;; its callbacks did to objects (L3.budget.exhausted)
                             ((get-in st [:dyn :on-exhausted]) (assoc st ::in-host true))
                             (throw ex))
                           (raise st ex)))))]
          (if (= :done (:mode r)) r (recur r))))
      (finally (.set context saved)))))

;; ---------------------------------------------------------------------------
;; Entry points

(defn eval-term
  "Evaluate `term` in a fresh activation: world, mint nil, dynamic context."
  [term world dyn]
  (:ctl (run-state (state :eval (prepare-term term) [] () world nil dyn))))

(defn call-in
  "Call function value `f` with `args` from host code, in the context of the
   innermost running machine (L3.effect.host-boundary). With `deopt?` (calls
   from compiled code) any effect the callee does not handle itself abandons
   the compiled call (L4.exec.leave)."
  [[world mint dyn _ _ outer-k] f args & [deopt?]]
  (let [r (run-state (state :apply [f (vec args)] nil
                            (ks/push ks/empty-stack (ks/boundary-frame deopt? outer-k)) world mint dyn))]
    ;; the caller goes on in the world the callback left (L1.def.read-your-writes)
    (when-let [^objects c (.get context)] (aset c 0 (:world r)))
    (:ctl r)))

(reset! v/host-invoke
        (fn [f args]
          (let [ctx (current-context)]
            (when-not ctx
              (fail :L3.effect.host-boundary
                    "a Klara function was called by host code outside any Klara activation"))
            (call-in (vec ctx) f args))))
