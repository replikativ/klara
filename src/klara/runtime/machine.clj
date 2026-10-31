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
  klara.lang.builtins) are called with the state and return a new state."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Closure Continuation Code CodeVar World]))

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; Raised inside nested machines and compiled code to abandon them without
;; observable effects (L4.exec.deopt): exhaustion and boundary-crossing effects.
(defrecord Abandon [reason])
(defn abandon! [reason] (throw (ex-info "abandon" {::abandon reason})))
(defn abandoned [^Throwable e] (when (instance? clojure.lang.ExceptionInfo e) (::abandon (ex-data e))))

(def ^:dynamic *nested*
  "The state from which host code was called, if any; host calls back into
   Klara closures run a nested machine in that context."
  nil)

;; Hooks set by later layers (L4): select a compiled implementation of a
;; definition, and call an executable.
(defonce resolve-hook (atom nil))     ; (fn [q definition world session] value-or-nil)

;; ---------------------------------------------------------------------------
;; Intrinsic values

(defrecord Intrinsic [name f])

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

(def ^:private host-cache (java.util.concurrent.ConcurrentHashMap.))

(defn- host-lookup [q]
  (or (.get host-cache q)
      (let [x (host-value q)] (.put host-cache q x) x)))

;; ---------------------------------------------------------------------------
;; Globals (L2.link.*)

(defn resolve-link
  ([link world] (resolve-link link world nil))
  ([link ^World world session]
  (case (:kind link)
    :late (let [q (:name link)
                d (w/lookup world q)]
            (when (nil? d) (fail :L1.resolve.unbound (str "unable to resolve " q " in " (w/id world)) :name q))
            (or (when-let [h (and session @resolve-hook)] (h q d world session)) (:value d)))
    :pinned (w/pin (:world link) (:name link))
    :guarded (let [q (:name link)]
               (if (= (:generation link) (w/generation world q))
                 (:value link)
                 (resolve-link {:kind :late :name q} world session))))))

;; ---------------------------------------------------------------------------
;; Closure application

(defn- select-arity [^Closure f n]
  (let [as (:arities (.-term f))]
    (or (some (fn [[i a]] (when (and (nil? (:rest a)) (= n (count (:params a)))) [i a]))
              (map-indexed vector as))
        (some (fn [[i a]] (when (and (:rest a) (>= n (count (:params a)))) [i a]))
              (map-indexed vector as))
        (fail :L0.eval.arity (str "wrong number of arguments (" n ") passed to " f)))))

(defn- bind-args [env ^Closure f a args]
  (let [params (:params a)
        env (loop [env env ps params as args]
              (if (seq ps) (recur (assoc env (first ps) (first as)) (rest ps) (rest as)) env))
        env (if (:rest a) (assoc env (:rest a) (seq (drop (count params) args))) env)]
    (if-let [s (:self (.-term f))] (assoc env s f) env)))

(defn- closure-env
  "The environment a closure body starts in: its captured locals."
  [^Closure f] (.-env f))

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

(defn- constructing
  "Fresh names bound by code constructions still in progress on `k`
   (L2.code.extrusion is checked against the dynamic extent of construction)."
  [k]
  (or (some #(when (= :code (:f %)) (:bound %)) k) #{}))

(defn- instantiate
  "Finish a :code term: holes have been evaluated to Code values. `allowed`
   are the fresh names of enclosing constructions in progress."
  [term env allowed tmpl hole-values]
  (let [bodies (mapv (fn [c] (if (v/code? c) (.-term ^Code c)
                                 (fail :L2.esc.not-code (str "esc must produce code, got " (pr-str c)))))
                     hole-values)
        spliced (splice-holes tmpl (:id term) bodies)
        subst (into {} (map (fn [n]
                              (let [x (get env n)]
                                [n (if (instance? CodeVar x) (t/local (:name x)) (lift-term x))])))
                    (:free term))
        result (t/refresh-free (t/substitute spliced subst))
        allowed (into allowed (keep (fn [[_ x]] (when (instance? CodeVar x) (:name x)))) env)
        free (t/free-locals result)
        extruded (remove allowed free)]
    (when (seq extruded)
      (fail :L2.code.extrusion
            (str "code refers to " (first extruded) " outside the code that binds it")
            :locals (vec extruded)))
    (Code. result)))

;; ---------------------------------------------------------------------------
;; The machine

(declare run-state)

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
          (abandon! :effect)                                      ; L4.exec.deopt
        (fail (if (= kind :stop) (if (= :boundary (:f (nth k i))) :L3.effect.host-boundary :L3.effect.unhandled)
                :L3.effect.unhandled)
              (str "unhandled effect " op) :op op))))))

(defn- raise
  "Unwind `st` with exception `ex` to the nearest try or job frame (L0.eval.exception)."
  [st ^Throwable ex]
  (loop [k (:k st)]
    (if-let [f (first k)]
      (case (:f f)
        :try (if-let [c (some #(when (instance? (:class %) ex) %) (:catches f))]
               (let [env (assoc (:env f) (:name c) ex)
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

(defn- recur-args
  "recur binds the rest parameter to its argument directly (L0.eval.tail)."
  [env ^Closure f a args]
  (let [n (count (:params a))
        env (reduce (fn [e [p x]] (assoc e p x)) env (map vector (:params a) args))
        env (if (:rest a) (assoc env (:rest a) (nth args n)) env)]
    (if-let [s (:self (.-term f))] (assoc env s f) env)))

(declare raise)

(defn- job-snapshot [st] (when-let [j (get-in st [:dyn :job])] @j))

(defn- apply-value
  "Apply function value `f` to `args` (L0.eval.call)."
  [st f args recur-arity]
  (cond
    (instance? Closure f)
    (let [^Closure f f
          a (if recur-arity (nth (:arities (.-term f)) recur-arity) (second (select-arity f (count args))))
          env (if recur-arity (recur-args (closure-env f) f a args) (bind-args (closure-env f) f a args))
          basis (.-basis f)]
      (if (and basis (not (identical? basis (:mint st))))
        ;; L1.context.call-based: run in the basis, restore afterwards
        (let [k (:k st)
              k (if (= :restore (:f (first k))) k
                  (conj k {:f :restore :world (:world st) :mint (:mint st)}))]
          (assoc st :mode :eval :ctl (:body a) :env env :k k :world basis :mint basis))
        (assoc st :mode :eval :ctl (:body a) :env env)))

    (instance? Continuation f)
    (let [^Continuation f f]
      (when-not (= 1 (count args)) (fail :L0.eval.arity "a continuation takes one argument"))
      (assoc st :mode :ret :ctl (first args) :env nil
             :k (reduce conj (:k st) (rseq (.-frames f)))
             :world (.-world f) :mint (.-mint f)))

    (instance? Intrinsic f)
    ((:f f) st args)

    (instance? klara.runtime.value.IExecutable f)
    (v/-execute f st args)

    :else
    (let [snapshot (job-snapshot st)
          r (try (binding [*nested* st] (apply f args))
                 (catch Throwable ex
                   (when (abandoned ex)
                     ;; nothing the abandoned host call did may survive (L4.exec.deopt)
                     (when snapshot (reset! (get-in st [:dyn :job]) snapshot))
                     (throw ex))
                   (reduced ex)))]
      (if (reduced? r) (raise st @r) (assoc st :mode :ret :ctl r :env nil)))))

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

(defn- charge [st]
  (when-let [^longs m (get-in st [:dyn :meter])]
    (let [n (dec (aget m 0))]
      (aset m 0 n)
      (neg? n))))

(defn- step-eval [st]
  (let [c (:ctl st) env (:env st) k (:k st)]
    (case (:op c)
      :const (assoc st :mode :ret :ctl (:value c))
      :local (let [n (:name c)]
               (if (contains? env n)
                 (let [x (get env n)] (assoc st :mode :ret :ctl (if (instance? RecRef x) @x x)))
                 (fail :L0.term.wf (str "unbound local " n))))
      :global (assoc st :mode :ret :ctl (resolve-link (:link c) (:world st) (get-in st [:dyn :session])))
      :host (assoc st :mode :ret :ctl (host-lookup (:name c)))
      :fn (let [captured (persistent! (reduce (fn [m n] (assoc! m n (get env n))) (transient {}) (:free c)))]
            (assoc st :mode :ret :ctl (Closure. c captured (:mint st))))
      :app (assoc st :ctl (:fn c) :k (conj k {:f :args :todo (:args c) :vals [] :env env :recur (:recur c)}))
      :let (assoc st :ctl (:init c) :k (conj k {:f :let :name (:name c) :body (:body c) :env env}))
      :letrec (let [refs (into {} (map (fn [[n _]] [n (rec-ref)])) (:bindings c))
                    env' (merge env refs)
                    fns (mapv (fn [[n f]]
                                [n (Closure. f (into {} (map (fn [x] [x (get env' x)])) (:free f)) (:mint st))])
                              (:bindings c))]
                (doseq [[n f] fns] (set-rec! (get refs n) f))
                (assoc st :ctl (:body c) :env (into env fns)))
      :if (assoc st :ctl (:test c) :k (conj k {:f :if :then (:then c) :else (:else c) :env env}))
      :do (let [[x & more] (:body c)]
            (if more (assoc st :ctl x :k (conj k {:f :do :rest more :env env})) (assoc st :ctl x)))
      :recur (assoc st :ctl {:op :app :fn (t/local (:target c)) :args (:args c) :recur (:arity c)})
      :throw (assoc st :ctl (:ex c) :k (conj k {:f :throw}))
      :try (assoc st :ctl (:body c)
                  :k (conj k {:f :try :catches (:catches c) :finally (:finally c) :env env
                              :world (:world st) :mint (:mint st)}))
      :interop (if (seq (t/children c))
                 (let [[x & more] (t/children c)]
                   (assoc st :ctl x :k (conj k {:f :interop :term c :todo more :vals [] :env env})))
                 (assoc st :mode :ret :ctl (interop c [])))
      :def (do (when (:mint st)
                 (fail :L1.def.pinned (str "def of " (:name c) " in a pinned context")))
               (assoc st :ctl (:init c) :k (conj k {:f :def :term c})))
      :code (let [[tmpl renaming] (t/freshen (:template c))
                  hole-env (reduce (fn [e [old new]] (assoc e old (v/->CodeVar new))) env renaming)
                  holes (:holes c)]
              (if (seq holes)
                (assoc st :ctl (first holes) :env hole-env
                       :k (conj k {:f :code :term c :env env :hole-env hole-env :tmpl tmpl
                                   :bound (into (constructing k) (vals renaming))
                                   :todo (rest holes) :vals []}))
                (assoc st :mode :ret :ctl (instantiate c env (constructing k) tmpl []))))
      (fail :L0.term.wf (str "unknown term " (:op c))))))

(defn- step-ret [st]
  (let [x (:ctl st) k (:k st) f (first k) k (rest k)]
    (case (:f f)
      :args (let [vals (conj (:vals f) x)]
              (if-let [[t & more] (seq (:todo f))]
                (assoc st :mode :eval :ctl t :env (:env f) :k (conj k (assoc f :todo more :vals vals)))
                (assoc st :mode :apply :ctl [(first vals) (subvec vals 1) (:recur f)] :k k)))
      :let (assoc st :mode :eval :ctl (:body f) :env (assoc (:env f) (:name f) x) :k k)
      :if (assoc st :mode :eval :ctl (if x (:then f) (:else f)) :env (:env f) :k k)
      :do (let [[t & more] (:rest f)]
            (assoc st :mode :eval :ctl t :env (:env f) :k (if more (conj k (assoc f :rest more)) k)))
      :restore (assoc st :k k :world (:world f) :mint (:mint f))
      :handle (if-let [r (:return f)]
                (assoc st :mode :apply :ctl [r [x]] :k k :world (:world f) :mint (:mint f))
                (assoc st :k k))
      :try (if (:finally f)
             (assoc st :mode :eval :ctl (:finally f) :env (:env f)
                    :k (conj k {:f :finally-value :value x}))
             (assoc st :k k))
      :finally-value (assoc st :ctl (:value f) :k k)
      :finally-ret (assoc st :mode :eval :ctl (:term f) :env (:env f) :k (conj k {:f :finally-value :value x}))
      :finally-throw (raise (assoc st :k k) (:ex f))
      :throw (raise (assoc st :k k)
                    (if (instance? Throwable x) x
                        (ex-info (str "throw of a non-throwable: " (pr-str x)) {:rule :L0.eval.exception :value x})))
      :interop (let [vals (conj (:vals f) x)]
                 (if-let [[t & more] (seq (:todo f))]
                   (assoc st :mode :eval :ctl t :env (:env f) :k (conj k (assoc f :todo more :vals vals)))
                   (let [r (try (interop (:term f) vals) (catch Throwable ex (reduced ex)))]
                     (if (reduced? r) (raise (assoc st :k k) @r) (assoc st :ctl r :k k)))))
      :def (let [c (:term f)]
             (perform (assoc st :k k) :world/define
                      [(:name c) {:form (:form c) :term (:init c) :value x :macro? (:macro? c)}]))
      :code (let [vals (conj (:vals f) x)]
              (if-let [[t & more] (seq (:todo f))]
                (assoc st :mode :eval :ctl t :env (:hole-env f) :k (conj k (assoc f :todo more :vals vals)))
                (let [r (try (instantiate (:term f) (:env f) (constructing k) (:tmpl f) vals) (catch Throwable ex (reduced ex)))]
                  (if (reduced? r) (raise (assoc st :k k) @r) (assoc st :ctl r :k k)))))
      :job ((:on-return f) (assoc st :k k) f x)
      :boundary (assoc st :mode :done :k k)
      :frame-fn ((:fn f) (assoc st :k k) x))))

(defn- stop-frame [k] (some #(#{:job :boundary} (:f %)) k))

(defn- exhaust
  "The budget ran out in `st` (L3.budget.exhausted). Inside a nested machine
   the host call is abandoned; the job that owns the budget then suspends
   at that call."
  [st]
  (if (= :job (stop-frame (:k st)))
    ((get-in st [:dyn :on-exhausted]) st)
    (abandon! :exhausted)))

(defn- guarded [st f]
  (try (f st)
       (catch Throwable ex
         (if-let [reason (abandoned ex)]
           (if (and (= reason :exhausted) (= :job (stop-frame (:k st))))
             ((get-in st [:dyn :on-exhausted]) st)
             (throw ex))
           (raise st ex)))))

(defn step [st]
  (case (:mode st)
    :eval (if (charge st) (exhaust st) (guarded st step-eval))
    :ret (if (empty? (:k st)) (assoc st :mode :done) (guarded st step-ret))
    :apply (guarded st (fn [st] (let [[f args r] (:ctl st)] (apply-value st f args r))))))

(defn run-state
  "Run `st` until it returns from its last frame. Returns the final state."
  [st]
  (loop [st st]
    (if (= :done (:mode st)) st (recur (step st)))))

;; ---------------------------------------------------------------------------
;; Entry points

(defn eval-term
  "Evaluate `term` in a fresh activation: world, mint nil, dynamic context."
  [term world dyn]
  (:ctl (run-state (state :eval term {} () world nil dyn))))

(defn call-in
  "Call function value `f` with `args` from a host context (nested machine,
   L3.effect.host-boundary). `outer` is the calling state. With `deopt?`
   (calls from compiled code) any effect the callee does not handle itself
   abandons the compiled call (L4.exec.deopt)."
  [outer f args & [deopt?]]
  (let [st (state :apply [f (vec args)] nil (list {:f :boundary :deopt deopt?})
                  (:world outer) (:mint outer) (:dyn outer))]
    (:ctl (run-state st))))

(reset! v/host-invoke
        (fn [f args]
          (let [outer *nested*]
            (when-not outer
              (fail :L3.effect.host-boundary
                    "a Klara function was called by host code outside any Klara activation"))
            (call-in outer f args))))
