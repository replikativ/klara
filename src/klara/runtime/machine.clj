(ns klara.runtime.machine
  "The reference semantics: a CEK machine (spec/L0-core.md#evaluation).

  A state is
    mode   :eval (ctl is a term, evaluated in env) or :ret (ctl is a value)
    k      the continuation: a list of frames, top first; frames are maps
    world  the effective world E      (L1.context.*)
    mint   the basis stamped on new closures, nil or a world
    dyn    {:meter :defaults :session :job}: what belongs to the caller
           rather than to the code (budget, default handlers)

  Every frame is plain data, so a continuation is a vector of frames and
  resuming it pushes them back: handlers are deep and continuations
  multi-shot (L3.handle.deep, L3.cont.multishot). Calls in tail position push
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

(defn- bind-args
  "The body environment: captured locals, the function itself if used, the
   parameters and (for a call) the rest argument as a seq, or (for recur) the
   rest argument as given."
  [^Closure f ^klara.runtime.prepare.Arity a args recur?]
  (let [env (.-env f)
        env (if (.-self? a) (conj env f) env)
        n (.-nparams a)
        env (loop [env env i 0]
              (if (< i n) (recur (conj env (nth args i)) (inc i)) env))]
    (if (.-rest? a)
      (conj env (if recur? (nth args n) (seq (subvec (vec args) n))))
      env)))

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

(defn constructing
  "Fresh names bound by code constructions still in progress on `k`
   (L2.code.extrusion is checked against the dynamic extent of construction).
   A :binders frame (klara.jit/function) binds names the same way."
  [k]
  (or (some #(when (#{:code :binders} (:f %)) (:bound %)) k) #{}))

(defn- instantiate
  "Finish a code node: holes have been evaluated to Code values. `allowed`
   are the fresh names of enclosing constructions in progress."
  [^klara.runtime.prepare.Code node env allowed tmpl hole-values]
  (let [term (.-term node)
        bodies (mapv (fn [c] (if (v/code? c) (.-term ^Code c)
                                 (fail :L2.esc.not-code (str "esc must produce code, got " (pr-str c)))))
                     hole-values)
        spliced (splice-holes tmpl (:id term) bodies)
        subst (into {} (map (fn [[n slot]]
                              (let [x (nth env slot)
                                    x (if (instance? RecRef x) @x x)]
                                [n (if (instance? CodeVar x) (t/local (:name x)) (lift-term x))])))
                    (.-free-slots node))
        result (t/refresh-free (t/substitute spliced subst))
        allowed (into allowed (keep (fn [x] (when (instance? CodeVar x) (:name x)))) env)
        free (t/free-locals result)
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
  "Set the context host code observes (compiled code, host callbacks)."
  [world mint dyn]
  (let [^objects h (.get context)] (aset h 0 world) (aset h 1 mint) (aset h 2 dyn)))

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

(defn- find-handler
  "Index of the nearest handle frame for `op`, or the index of the first
   frame that stops the search (:job, :boundary), or nil."
  [k op]
  (loop [k k i 0]
    (when-let [f (first k)]
      (case (:f f)
        :handle (if (contains? (:handlers f) op) [:handler i] (recur (rest k) (inc i)))
        (:job :boundary) [:stop i]
        (recur (rest k) (inc i))))))

(defn perform
  "Perform `op` with `args` from state `st` (L3.perform.op)."
  [st op args]
  (let [k (:k st)
        [kind i] (find-handler k op)]
    (if (= kind :handler)
      (let [captured (vec (take (inc i) k))
            frame (nth captured i)
            cont (Continuation. captured (:world st) (:mint st))
            handler (get (:handlers frame) op)]
        ;; the handler runs outside its frame, in the handle expression's context
        (assoc st :mode :apply :ctl [handler (into [cont] args)]
               :k (nthrest k (inc i)) :world (:world frame) :mint (:mint frame)))
      (if-let [d (and (not (and (= kind :stop) (:deopt (nth k i)))) (get-in st [:dyn :defaults op]))]
        (d st args)
        (if (and (= kind :stop) (:deopt (nth k i)))
          ;; L4.exec.leave: hand the whole state to the compiled caller
          (throw (ex-info "leave nested machine" {::abandon :effect ::state st}))
          (fail (if (and (= kind :stop) (= :boundary (:f (nth k i)))) :L3.effect.host-boundary :L3.effect.unhandled)
                (str "unhandled effect " op) :op op))))))

;; ---------------------------------------------------------------------------
;; Klara stack traces (L0.trace.positions)

(def ^:private traced (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn- node-pos [x]
  (when (instance? klara.runtime.prepare.INode x)
    (:pos (.sourceTerm ^klara.runtime.prepare.INode x))))

(defn- frame-pos [f]
  (some node-pos [(:body f) (:then f) (:node f) (first (:todo f)) (:term f)]))

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
      (case (:f f)
        :try (if-let [c (some #(when (instance? (:class %) ex) %) (:catches f))]
               (let [env (conj (:env f) ex)
                     k (if (:finally f) (conj (rest k) {:f :finally-ret :term (:finally f) :env (:env f)}) (rest k))]
                 (assoc st :mode :eval :ctl (:body c) :env env :k k :world (:world f) :mint (:mint f)))
               (if (:finally f)
                 (assoc st :mode :eval :ctl (:finally f) :env (:env f)
                        :k (conj (rest k) {:f :finally-throw :ex ex}) :world (:world f) :mint (:mint f))
                 (recur (rest k))))
        :job ((:on-throw f) (assoc st :k (rest k)) f ex)
        :boundary (throw ex)
        (recur (rest k)))
      (throw ex))))

(defn- stop-frame [k] (some #(#{:job :boundary} (:f %)) k))

(defn- exhaust
  "The budget ran out in `st` (L3.budget.exhausted). Inside a nested machine
   the host call is abandoned; the job that owns the budget then suspends
   at that call."
  [st]
  (let [stop (some #(when (#{:job :boundary} (:f %)) %) (:k st))]
    (cond
      (= :job (:f stop)) ((get-in st [:dyn :on-exhausted]) st)
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
  [args env world mint dyn]
  (case (count args)
    0 []
    1 [(imm (nth args 0) env world mint dyn)]
    2 (let [a (imm (nth args 0) env world mint dyn)] [a (imm (nth args 1) env world mint dyn)])
    3 (let [a (imm (nth args 0) env world mint dyn) b (imm (nth args 1) env world mint dyn)]
        [a b (imm (nth args 2) env world mint dyn)])
    (mapv #(imm % env world mint dyn) args)))

(defn- imm-prefix
  "Evaluate the leading immediate argument nodes. Returns [values remaining],
   where `remaining` starts at the first non-immediate node (or is nil)."
  [args env world mint dyn]
  (loop [args (seq args) out (transient [])]
    (if (nil? args)
      [(persistent! out) nil]
      (let [x (imm (first args) env world mint dyn)]
        (if (identical? x none)
          [(persistent! out) args]
          (recur (next args) (conj! out x)))))))

(defn- imm
  "The value of node `c` if it is immediate, else `none`."
  [c env world mint dyn]
  (case (prep/tag c)
    0 (.-value ^klara.runtime.prepare.Const c)
    1 (let [x (nth env (.-slot ^klara.runtime.prepare.Local c))]
        (if (instance? RecRef x) @x x))
    2 (resolve-global c world dyn)
    3 (.-value ^klara.runtime.prepare.Host c)
    4 (let [^klara.runtime.prepare.Fn c c
            cap (.-captured c)]
        (Closure. (.-term c) c (case (count cap)
                                 0 []
                                 1 [(nth env (nth cap 0))]
                                 2 [(nth env (nth cap 0)) (nth env (nth cap 1))]
                                 (mapv #(nth env %) cap))
                  mint))
    5 (let [^klara.runtime.prepare.App c c]
        (if (.-flat c)
          (let [hf (.-value ^klara.runtime.prepare.Host (.-f c))
                vals (imm-all (.-args c) env world mint dyn)]
            (when-not (instance? clojure.lang.IFn hf)
              (fail :L0.eval.not-fn (str "cannot call " (pr-str hf) ": not a function")))
            (set-context! world mint dyn)
            (invoke-host hf vals))
          none))
    none))

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

(defn- self-call-frame?
  "Is args frame f completing a definition's call of itself?"
  [f]
  (let [n (:node f)]
    (and (instance? klara.runtime.prepare.App n) (.-self-call ^klara.runtime.prepare.App n))))

(defn- record-entry!
  "L4.profile.record: a function entry (or loop iteration) with its arguments."
  [dyn ^Closure f args external]
  (when (profiling? dyn)
    (.enter ^klara.runtime.prepare.IProfile (.-profile ^klara.runtime.prepare.Fn (.-node f)) args (boolean external))))

(defn- record-call! [dyn ^klara.runtime.prepare.App c fv]
  (when (and (profiling? dyn) (or (instance? Closure fv) (instance? klara.runtime.value.IExecutable fv)))
    (.call ^klara.runtime.prepare.IProfile (.-profile c) fv)))

(defn- record-branch! [dyn ^klara.runtime.prepare.If c x]
  (when (profiling? dyn) (.branch ^klara.runtime.prepare.IProfile (.-profile c) (boolean x))))

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
        world (aget regs 4) mint (aget regs 5) dyn (aget regs 6)]
      (let [c ctl
            x (imm c env world mint dyn)]
        (if-not (identical? x none)
          (next! regs :ret x env k world mint dyn)
          (case (prep/tag c)
            5 (let [^klara.runtime.prepare.App c c
                    fv (imm (.-f c) env world mint dyn)
                    _ (when-not (identical? fv none) (record-call! dyn c fv))]
                (cond
                  (identical? fv none)
                  (next! regs :eval (.-f c) env (conj k {:f :args :node c :todo (.-args c) :vals [] :env env :recur (.-recur-arity c)}) world mint dyn)
                  (and (.-all-imm c) (instance? Closure fv) (nil? (.-basis ^Closure fv)) (not (charge! (:meter dyn))))
                  ;; the common case: an open closure on immediate arguments, entered directly
                  (let [^Closure fv fv
                        args (imm-all (.-args c) env world mint dyn)
                        ra (.-recur-arity c)
                        i (if ra (long ra) (select-arity fv (count args)))
                        ^klara.runtime.prepare.Arity a (nth (.-arities ^klara.runtime.prepare.Fn (.-node fv)) i)]
                    (record-entry! dyn fv args (not (.-self-call c)))
                    (next! regs :eval (.-body a) (bind-args fv a args (boolean ra)) k world mint dyn))
                  (.-all-imm c)
                  (next! regs :apply [fv (imm-all (.-args c) env world mint dyn) (.-recur-arity c) (.-self-call c)] env k world mint dyn)
                  :else
                  (let [[vals remaining] (imm-prefix (.-args c) env world mint dyn)]
                    (if (nil? remaining)
                      (next! regs :apply [fv vals (.-recur-arity c) (.-self-call c)] env k world mint dyn)
                      (next! regs :eval (first remaining) env
                             (conj k {:f :args :node c :todo (next remaining) :vals (into [fv] vals) :env env :recur (.-recur-arity c)})
                             world mint dyn)))))
            6 (let [^klara.runtime.prepare.Let c c
                    x (imm (.-init c) env world mint dyn)]
                (if (identical? x none)
                  (next! regs :eval (.-init c) env (conj k {:f :let :body (.-body c) :env env}) world mint dyn)
                  (next! regs :eval (.-body c) (conj env x) k world mint dyn)))
            8 (let [^klara.runtime.prepare.If c c
                    x (imm (.-test c) env world mint dyn)]
                (if (identical? x none)
                  (next! regs :eval (.-test c) env (conj k {:f :if :node c :then (.-then c) :else (.-else c) :env env}) world mint dyn)
                  (do (record-branch! dyn c x)
                      (next! regs :eval (if x (.-then c) (.-else c)) env k world mint dyn))))
            9 (let [^klara.runtime.prepare.Do c c
                    exprs (.-exprs c)]
                (if (seq exprs)
                  (next! regs :eval (first exprs) env (conj k {:f :do :rest (concat (rest exprs) [(.-last c)]) :env env}) world mint dyn)
                  (next! regs :eval (.-last c) env k world mint dyn)))
            7 (let [^klara.runtime.prepare.Letrec c c
                    fns (.-fns c)
                    refs (mapv (fn [_] (rec-ref)) fns)
                    env' (into env refs)]
                (doseq [[r ^klara.runtime.prepare.Fn f] (map vector refs fns)]
                  (set-rec! r (Closure. (.-term f) f (mapv #(nth env' %) (.-captured f)) mint)))
                (next! regs :eval (.-body c) env' k world mint dyn))
            10 (let [^klara.runtime.prepare.Recur c c
                     self (let [x (nth env (.-slot c))] (if (instance? RecRef x) @x x))]
                 (if (and (.-all-imm c) (nil? (.-basis ^Closure self)) (not (charge! (:meter dyn))))
                   ;; a loop iteration: re-enter the arity directly (L0.eval.tail)
                   (let [^Closure self self
                         fnode (.-node self)
                         ^klara.runtime.prepare.Arity a (nth (.-arities ^klara.runtime.prepare.Fn fnode) (.-arity c))
                         args (imm-all (.-args c) env world mint dyn)
                         osr (.osr ^klara.runtime.prepare.IOsr fnode)
                         compiled (when osr (osr self world mint))]
                     (if compiled
                       ;; L4.exec.osr: compiled code for this loop exists and holds here
                       (next! regs :apply [compiled args nil] env k world mint dyn)
                       (do (record-entry! dyn self args true)
                           (next! regs :eval (.-body a) (bind-args self a args true) k world mint dyn))))
                 (let [[vals remaining] (if (.-all-imm c)
                                        [(imm-all (.-args c) env world mint dyn) nil]
                                        (imm-prefix (.-args c) env world mint dyn))]
                 (if (nil? remaining)
                   (next! regs :apply [self vals (.-arity c)] env k world mint dyn)
                   (next! regs :eval (first remaining) env
                          (conj k {:f :args :node c :todo (next remaining) :vals (into [self] vals) :env env :recur (.-arity c)})
                          world mint dyn)))))
            11 (next! regs :eval (.-ex ^klara.runtime.prepare.Throw c) env (conj k {:f :throw}) world mint dyn)
            12 (let [^klara.runtime.prepare.Try c c]
                 (next! regs :eval (.-body c) env
                        (conj k {:f :try :catches (.-catches c) :finally (.-finally c) :env env :world world :mint mint})
                        world mint dyn))
            13 (let [^klara.runtime.prepare.Interop c c
                     cs (.-args c)]
                 (if (seq cs)
                   (next! regs :eval (first cs) env (conj k {:f :interop :term (.-term c) :todo (rest cs) :vals [] :env env}) world mint dyn)
                   (next! regs :ret (do (set-context! world mint dyn) (interop (.-term c) [])) env k world mint dyn)))
            14 (let [^klara.runtime.prepare.Def c c]
                 (when mint (fail :L1.def.pinned (str "def of " (:name (.-term c)) " in a pinned context")))
                 (next! regs :eval (.-init c) env (conj k {:f :def :term (.-term c)}) world mint dyn))
            15 (let [^klara.runtime.prepare.Code c c
                     term (.-term c)
                     [tmpl renaming] (t/freshen (:template term))
                     hole-env (into env (map (fn [b] (v/->CodeVar (get renaming b b)))) (.-binders c))
                     holes (.-holes c)]
                 (if (seq holes)
                   (next! regs :eval (first holes) hole-env
                          (conj k {:f :code :node c :env env :hole-env hole-env :tmpl tmpl
                                   :bound (into (constructing k) (vals renaming))
                                   :todo (rest holes) :vals []})
                          world mint dyn)
                   (next! regs :ret (instantiate c env (constructing k) tmpl []) env k world mint dyn)))
            (fail :L0.term.wf (str "unknown node " c)))))))

(defn- step-ret [regs]
  (let [^objects regs regs
        mode (aget regs 0) ctl (aget regs 1) env (aget regs 2) k (aget regs 3)
        world (aget regs 4) mint (aget regs 5) dyn (aget regs 6)]
      (if (empty? k)
        (state :done ctl env k world mint dyn)
        (let [x ctl f (first k) k (rest k)]
          (case (:f f)
            :args (let [vals (conj (:vals f) x)]
                    (if-let [todo (seq (:todo f))]
                      (let [[more remaining] (imm-prefix todo (:env f) world mint dyn)
                            vals (into vals more)]
                        (if (nil? remaining)
                          (next! regs :apply [(first vals) (subvec vals 1) (:recur f) (self-call-frame? f)] env k world mint dyn)
                          (next! regs :eval (first remaining) (:env f)
                                 (conj k (assoc f :todo (next remaining) :vals vals)) world mint dyn)))
                      (next! regs :apply [(first vals) (subvec vals 1) (:recur f) (self-call-frame? f)] env k world mint dyn)))
            :let (next! regs :eval (:body f) (conj (:env f) x) k world mint dyn)
            :if (do (record-branch! dyn (:node f) x)
                    (next! regs :eval (if x (:then f) (:else f)) (:env f) k world mint dyn))
            :do (let [[a & more] (:rest f)]
                  (next! regs :eval a (:env f) (if more (conj k (assoc f :rest more)) k) world mint dyn))
            :restore (next! regs :ret x env k (:world f) (:mint f) dyn)
            :restore-profile (next! regs :ret x env k world mint
                                    (if (:no-profile f) (assoc dyn :no-profile true) (dissoc dyn :no-profile)))
            :binders (next! regs :ret x env k world mint dyn)
            :handle (if-let [r (:return f)]
                      (next! regs :apply [r [x]] env k (:world f) (:mint f) dyn)
                      (next! regs :ret x env k world mint dyn))
            :try (if (:finally f)
                   (next! regs :eval (:finally f) (:env f) (conj k {:f :finally-value :value x}) world mint dyn)
                   (next! regs :ret x env k world mint dyn))
            :finally-value (next! regs :ret (:value f) env k world mint dyn)
            :finally-ret (next! regs :eval (:term f) (:env f) (conj k {:f :finally-value :value x}) world mint dyn)
            :finally-throw (raise (state :ret x env k world mint dyn) (:ex f))
            :throw (raise (state :ret x env k world mint dyn)
                          (if (instance? Throwable x) x
                              (ex-info (str "throw of a non-throwable: " (pr-str x)) {:rule :L0.eval.exception :value x})))
            :interop (let [vals (conj (:vals f) x)]
                       (if-let [[a & more] (seq (:todo f))]
                         (next! regs :eval a (:env f) (conj k (assoc f :todo more :vals vals)) world mint dyn)
                         (next! regs :ret (do (set-context! world mint dyn) (interop (:term f) vals)) env k world mint dyn)))
            :def (let [c (:term f)]
                   (perform (state :ret x env k world mint dyn) :world/define
                            [(:name c) {:form (:form c) :term (:init c) :value x :macro? (:macro? c) :meta (:meta c)}]))
            :code (let [vals (conj (:vals f) x)]
                    (if-let [[a & more] (seq (:todo f))]
                      (next! regs :eval a (:hole-env f) (conj k (assoc f :todo more :vals vals)) world mint dyn)
                      (next! regs :ret (instantiate (:node f) (:env f) (constructing k) (:tmpl f) vals) env k world mint dyn)))
            :job ((:on-return f) (state :ret x env k world mint dyn) f x)
            :boundary (state :done x env k world mint dyn)
            :frame-fn ((:fn f) (state :ret x env k world mint dyn) x))))))

(defn- step-apply [regs]
  (let [^objects regs regs
        mode (aget regs 0) ctl (aget regs 1) env (aget regs 2) k (aget regs 3)
        world (aget regs 4) mint (aget regs 5) dyn (aget regs 6)]
      (let [[fv args recur-arity] ctl]
        (cond
          (instance? Closure fv)
          (if (charge! (:meter dyn))
            (exhaust (state :apply ctl env k world mint dyn))
            (let [^Closure fv fv
                  i (if recur-arity (long recur-arity) (select-arity fv (count args)))
                  ^klara.runtime.prepare.Arity a (nth (.-arities ^klara.runtime.prepare.Fn (.-node fv)) i)
                  _ (record-entry! dyn fv args (not (get ctl 3)))
                  env' (bind-args fv a args (boolean recur-arity))
                  basis (.-basis fv)]
              (if (and basis (not (identical? basis mint)))
                ;; L1.context.call-based: run in the basis, restore afterwards
                (next! regs :eval (.-body a) env'
                       (if (= :restore (:f (first k))) k (conj k {:f :restore :world world :mint mint}))
                       basis basis dyn)
                (next! regs :eval (.-body a) env' k world mint dyn))))

          (instance? Continuation fv)
          (let [^Continuation fv fv]
            (when-not (= 1 (count args)) (fail :L0.eval.arity "a continuation takes one argument"))
            (if (charge! (:meter dyn))
              (exhaust (state :apply ctl env k world mint dyn))
              (next! regs :ret (first args) nil (reduce conj k (rseq (.-frames fv))) (.-world fv) (.-mint fv) dyn)))

          (instance? Intrinsic fv)
          ((:f fv) (state :apply ctl env k world mint dyn) args)

          (instance? klara.runtime.value.IExecutable fv)
          (v/-execute fv (state :apply ctl env k world mint dyn) args)

          (not (instance? clojure.lang.IFn fv))
          (fail :L0.eval.not-fn (str "cannot call " (pr-str fv) ": not a function") :value (pr-str fv))

          :else
          (let [snapshot (job-snapshot dyn)
                r (try (set-context! world mint dyn) (invoke-host fv args)
                       (catch Throwable ex
                         (when (abandoned ex)
                           ;; nothing the abandoned host call did may survive (L4.exec.leave)
                           (when snapshot (reset! (:job dyn) snapshot))
                           (throw ex))
                         (reduced ex)))]
            (if (reduced? r)
              (raise (state :apply ctl env k world mint dyn) @r)
              (next! regs :ret r nil k world mint dyn)))))))

(defn- drive
  "The fast path: run steps until one returns a state map (a slow path:
   intrinsic, effect, exception, job, done). `regs` always holds the state of
   the current step, for the exception handler."
  [st ^objects regs]
  (save! regs (:mode st) (:ctl st) (:env st) (:k st) (:world st) (:mint st) (:dyn st))
  (loop []
    (let [r (case (aget regs 0)
              :eval (step-eval regs)
              :ret (step-ret regs)
              :apply (step-apply regs)
              :done (regs-state regs))]
      (if (nil? r) (recur) r))))

(defn run-state
  "Run state map `st` until it returns from its last frame. Returns the final
   state map."
  [st]
  (let [saved (.get context)
        regs (object-array 7)]
    (.set context (object-array 5))   ; world mint dyn, and the meter cached per dyn (see meter-of)
    (try
      (loop [st st]
        (let [r (try (drive st regs)
                     (catch Throwable ex
                       (let [st (regs-state regs)]
                         (if-let [reason (abandoned ex)]
                           (if (and (= reason :exhausted) (= :job (stop-frame (:k st))))
                             ((get-in st [:dyn :on-exhausted]) st)
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
  [[world mint dyn] f args & [deopt?]]
  (:ctl (run-state (state :apply [f (vec args)] nil (list {:f :boundary :deopt deopt?}) world mint dyn))))

(reset! v/host-invoke
        (fn [f args]
          (let [ctx (current-context)]
            (when-not ctx
              (fail :L3.effect.host-boundary
                    "a Klara function was called by host code outside any Klara activation"))
            (call-in (vec ctx) f args))))
