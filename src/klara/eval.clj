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
  (:require [clojure.main]
            [clojure.string]
            [klara.core :as core]
            [klara.code :as code]
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

(declare call-value call-value* locus-rec-call stage-perform start-code step-build step-ret-stage)

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
                   (:version
                    (w/publish! (:world *fiber*)
                                #(w/put-entry % sym {:kind :def :value v :reads #{}
                                                     :code-id (str "value:" (System/identityHashCode v))
                                                     :value-id (str "value:" (System/identityHashCode v))}))))})

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
        (if-let [h (or (reference-handlers op) (@extra-handlers op))]
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

(defn- finish [node vals env k]
  (case (:op node)
    :app (call-value* (first vals) (rest vals) env k)
    :prim (host-apply (core/prims (:name node)) vals env k)
    :perform (cond
               (:target node) (do-perform (first vals) (:name node) (rest vals) env k)
               (= "stage" (namespace (:name node))) (stage-perform (:name node) vals env k)
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
    :app        (eval-list c (into [(:fn c)] (:args c)) env k)
    :prim       (eval-list c (:args c) env k)
    :perform    (eval-list c (cond->> (:args c) (:target c) (into [(:target c)])) env k)
    :specialize (eval-list c (into [(:fn c)] (:args c)) env k)
    :code       (start-code c env k)
    :esc        (raise (ex-info "klara: esc outside code" {:klara/error :stage}) env k)
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
                [:ret v nil k])
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
        :stage/locus-rec
        (let [lr (LocusRec. (Object.))
              fr {:tag :locus-rec :id (.-id lr) :env env
                  :state (atom {:table {} :order [] :bindings {}})}]
          (call-value* a [lr] env (conj k fr)))
        (raise (ex-info (str "klara: no handler for " op) {:op op}) env k)))))

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

;; states: [:eval term env k] | [:build term env k] | [:ret value _ k]
;;         | [:finish node vals env k]
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
(defmethod print-method LocusRec [_ ^java.io.Writer w] (.write w "#<genletrec>"))
