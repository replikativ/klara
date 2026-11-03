(ns klara.compile.lower
  "The backend (spec/L4-compiler.md#lowering): checked Core terms to JVM
  classes through the Clojure compiler.

  A lowered function is a host fn. Late links are looked up in the effective
  world of the call (L4.lower.links), read from the machine's current
  context. Each lowering is compiled by `eval`, which uses a fresh class
  loader (L4.retain.classes).

  Leaving compiled code (L4.exec.frame-state). The candidate is put in
  A-normal form (klara.compile.anf) and prepared like any term
  (klara.runtime.prepare). Lowering walks the term and its prepared nodes
  together, so at every point where compiled code may leave it knows the
  interpreter node to continue at, which compiled locals fill which
  environment slots, and the `let` frames around the point. It leaves with
  a Leave that carries this state:

  - a failed speculation, `(if guard specialized reference)`, continues at
    the reference node (L4.exec.leave);
  - a callee that performs an effect, or whose budget runs out, in a nested
    machine: the nested machine's state is carried along;
  - the budget running out at a function entry: the call is applied again by
    the interpreter.

  A `try` (L4.lower.try) is a host try: a Leave from its body passes out
  with an interpreter :try frame carrying its catch and finally clauses, so
  the interpreter continues inside the same try; a Leave from a catch arm
  carries the finally clause; the finally clause runs in compiled code only
  when the try completes here, by a value or an exception.

  A Leave is a value, not an exception: compiled code returns it, and every
  let whose initializer may leave checks for it and adds its own frame on
  the way out (an instance test, no try, no allocation). The receiving
  executable rebuilds the whole continuation and the machine goes on from
  there: nothing is re-executed. Host code never sees a Leave: a compiled
  function that host code calls (an executable, a lambda passed to a host
  function) completes its Leave in a nested machine first."
  (:require [klara.compile.anf :as anf]
            [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.account :as acct]
            [klara.runtime.machine :as m]
            [klara.runtime.prepare :as prep]
            [klara.runtime.prims :as prims]
            [klara.runtime.stack :as ks]
            [klara.runtime.value :as v])
  (:import [klara.runtime.value Closure]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; ---------------------------------------------------------------------------
;; Leaving

(definterface ILeave (state []) (addFrames [frames]) (addFrame [frame]))

;; state is one of
;;   {:mode :eval :node n :env env}      continue at node n
;;   {:mode :apply :f f :args args}      apply f to args
;;   {:mode :nested :state st}           continue a nested machine's state
;; with :frames, the let frames collected on the way out, innermost first.
(deftype Leave [^:volatile-mutable st]
  ILeave
  (state [_] st)
  (addFrames [this frames] (set! st (update st :frames into frames)) this)
  (addFrame [this frame] (set! st (assoc st :frames (conj (:frames st) frame))) this))

(defn leave?
  "The leave state of `x` if it is a Leave, else nil."
  [x]
  (when (instance? Leave x) (.state ^Leave x)))

(defn- leave [state] (Leave. (assoc state :frames [])))

(defn leave-up
  "A Leave passing out of a let: add the let's frame and pass it on."
  [^Leave l frame]
  (.addFrame l frame))

(defn- array-local?
  "Does the host know local `a` (in macro environment env) to be an array?"
  [env a]
  (let [^clojure.lang.Compiler$LocalBinding lb (and (symbol? a) (get env a))]
    (boolean (and lb (.hasJavaClass lb) (.isArray (.getJavaClass lb))))))

;; Array reads in compiled code (L4.lower.arrays): where the host knows the
;; array's class (a hint, L4.lower.hint), its own access; otherwise, for an
;; array and a long index, java.lang.reflect.Array, not the host's reflection
;; (which looks the method up on every call and is slower than the
;; interpreter); anything else goes to the host's aget function, failing as
;; it fails
(defmacro array-get [a i]
  (if (array-local? &env a)
    (list 'clojure.core/aget a i)
    (let [x (gensym "a") j (gensym "i")]
      (list 'let* [x a j i]
            (list 'if (list 'and (list 'some? x) (list '.isArray (list '.getClass (with-meta x {:tag 'Object})))
                            (list 'instance? 'java.lang.Long j))
                  ;; canonical booleans, as the host's aget (Array.get boxes afresh)
                  (list 'clojure.lang.Reflector/prepRet (list '.getComponentType (list '.getClass (with-meta x {:tag 'Object})))
                        (list 'java.lang.reflect.Array/get x (list 'clojure.lang.RT/intCast j)))
                  (list '.invoke (with-meta (list 'var 'clojure.core/aget) {:tag 'clojure.lang.IFn}) x j))))))

(defmacro array-length [a]
  (if (array-local? &env a)
    (list 'clojure.core/alength a)
    (let [x (gensym "a")]
      (list 'let* [x a]
            (list 'if (list 'and (list 'some? x) (list '.isArray (list '.getClass (with-meta x {:tag 'Object}))))
                  (list 'java.lang.reflect.Array/getLength x)
                  (list '.invoke (with-meta (list 'var 'clojure.core/alength) {:tag 'clojure.lang.IFn}) x))))))

(defn leave-eval [node env] (leave {:mode :eval :node node :env env}))

(defn let-frame [body-node env] (ks/let-frame body-node env))

(defn try-frame
  "L4.lower.try: the interpreter's frame for a try whose body left compiled code."
  [catches finally env ^objects ctx]
  (ks/try-frame catches finally env (aget ctx 0) (aget ctx 1)))

(defn finally-frame
  "L4.lower.try: the frame that runs a try's finally clause after a catch arm
   that left compiled code."
  [finally env]
  (ks/finally-ret-frame finally env))

;; Stress testing: leave at function entries with probability `stress`, to
;; exercise frame states everywhere (as V8's --deopt-every-n-times does).
(defonce stress (atom nil))

;; read on every function entry: a flag in a final array, kept by a watch
(defonce ^"[Z" stressed (boolean-array 1))
(add-watch stress ::flag (fn [_ _ _ p] (aset stressed 0 (some? p))))

(defn tick!
  "L4.lower.steps: one step per function entry and loop iteration. True when
   compiled code must leave here: the budget ran out, or stress testing."
  []
  (let [^objects c (m/current-context)
        meter (m/meter-of c)]
    (or (when meter
          (aset meter 0 (dec (aget meter 0)))
          (neg? (aget meter 0)))
        (when (aget stressed 0)
          (when-let [p @stress] (< (Math/random) (double p)))))))

(defn tick-meter!
  "tick! with the meter fetched once per function entry (see entry-bindings)."
  [^longs meter]
  (or (when meter
        (aset meter 0 (dec (aget meter 0)))
        (neg? (aget meter 0)))
      (when (aget stressed 0)
        (when-let [p @stress] (< (Math/random) (double p))))))

;; Every compiled function body starts by fetching the context once; its
;; loops and call sites use these locals. Nested machines install their own
;; context array and restore this one, so it is stable while the body runs.
(def ^:private entry-bindings
  '[klara-ctx__ (klara.runtime.machine/current-context)
    klara-meter__ (klara.runtime.machine/meter-of klara-ctx__)
    klara-stress__ (clojure.core/aget klara.compile.lower/stressed 0)])

;; inline: outside a budgeted job (no meter) and without stress testing a
;; step costs two local tests, no call
(def ^:private tick-form
  '(if (if (nil? klara-meter__) klara-stress__ true)
     (klara.compile.lower/tick-meter! klara-meter__)
     false))

(defn count-entry!
  "One more entry of a counting candidate (unsynchronized: a lost count only
   makes the estimate coarser)."
  [^longs a]
  (aset a 0 (unchecked-inc (aget a 0))))

(defn interpreted
  "The interpreter's closure for a compiled function: its node and captured values."
  [fn-node captured]
  (Closure. (.-term ^klara.runtime.prepare.Fn fn-node) fn-node (mapv prims/freeze captured) nil))

(def leave-intrinsics
  "Intrinsics that compiled code calls by leaving (L4.exec.leave): the
   interpreter applies them to the rebuilt state, as it would itself."
  '#{klara.effect/perform klara.effect/handle*})

(defn leave-intrinsic
  "Leave to apply intrinsic `f` to `args` (owned values frozen, L4.check.in-place)."
  [f args]
  (leave {:mode :apply :f f :args (mapv prims/freeze args)}))

(defn leave-apply
  "Leave at a function entry: the interpreter applies the function again
   (owned arguments frozen, L4.check.in-place)."
  [fn-node captured args]
  (leave {:mode :apply :f (interpreted fn-node captured) :args (mapv prims/freeze args)}))

(defn resume
  "The machine state that continues `st`, the state in which an executable
   was entered, after compiled code left with `leave` (L4.exec.frame-state)."
  [st leave]
  (let [{:keys [mode frames]} leave
        k (ks/reinstate (:k st) (vec frames))]
    ;; built whole, not by assoc: this runs whenever compiled code leaves
    (case mode
      :eval (m/state :eval (:node leave) (:env leave) k (:world st) (:mint st) (:dyn st))
      :apply (m/state :apply [(:f leave) (vec (:args leave)) nil] nil k (:world st) (:mint st) (:dyn st))
      :nested (let [n (:state leave)
                    inner (ks/above-boundary (:k n))]
                (m/state (:mode n) (:ctl n) (:env n) (reduce conj k (reverse inner)) (:world n) (:mint n) (:dyn st))))))

;; ---------------------------------------------------------------------------
;; Calls

;; A call site of a late link: the world id and value of its last resolution,
;; as in the interpreter's globals (klara.runtime.prepare).
(definterface ISite (lookup [ctx q]) (direct [ctx q]))

;; direct: the callee's host function when it can be called without checks
;; (L4.lower.direct), cached per world like the value; ::none when it cannot.
(deftype Site [^:volatile-mutable entry ^:volatile-mutable dentry]
  ISite
  (direct [this c q]
    (let [^objects c c]
      (when (nil? (aget c 1))
        (let [world (aget c 0)
              id (.-id ^klara.runtime.value.World world)
              d (klara.runtime.prepare/entry-value dentry id)]
          (if d
            (when-not (identical? d ::none) d)
            (let [x (.lookup this c q)
                  f (when (instance? klara.runtime.value.IExecutable x) (v/-direct x world))]
              (set! dentry (klara.runtime.prepare.CacheEntry. id (or f ::none)))
              f))))))
  (lookup [_ c q]
    (let [^objects c c
          world (aget c 0)
          id (.-id ^klara.runtime.value.World world)]
      (or (klara.runtime.prepare/entry-value entry id)
          (let [x (m/resolve-link {:kind :late :name q} world)]
            (set! entry (klara.runtime.prepare.CacheEntry. id x))
            x)))))

(defn late [^ISite site ctx q] (.lookup site ctx q))

(defn direct ^clojure.lang.IFn [^ISite site ctx q] (.direct site ctx q))

(defn- nested
  "Run a Klara function in a nested machine. If it performs an effect it
   does not handle, or its budget runs out, its state leaves with it."
  [f args]
  (let [^objects c (m/current-context)]
    (try (m/call-in [(aget c 0) (aget c 1) (aget c 2)] f args true)
         (catch clojure.lang.ExceptionInfo e
           (if-let [st (::m/state (ex-data e))]
             (leave {:mode :nested :state st})
             (throw e))))))

(declare resume)

(defn complete
  "The value of `r` for host code: a Leave runs to its end in a nested
   machine (where an effect nobody inside handles is an error, as for any
   Klara function host code calls, L3.effect.host-boundary)."
  [r]
  (if-let [l (leave? r)]
    (let [^objects c (m/current-context)
          base {:mode :ret :ctl nil :env nil :k (ks/push ks/empty-stack (ks/boundary-frame false nil))
                :world (aget c 0) :mint (aget c 1) :dyn (aget c 2)}]
      (:ctl (m/run-state (resume base l))))
    r))

;; A function compiled code creates: host code calls it through IFn and gets
;; values; compiled code calls the raw function and sees its Leave.
(deftype Lambda [^clojure.lang.IFn raw]
  ;; the interpreter runs a compiled function in its own machine: a Leave
  ;; resumes there, with the caller's handlers in the continuation
  v/IExecutable
  (-execute [_ st args]
    (m/set-context! (:world st) (:mint st) (:dyn st))
    (let [r (apply raw args)]
      (if-let [l (leave? r)]
        (resume st l)
        (assoc st :mode :ret :ctl r :env nil))))
  (-call [_ world mint dyn args] (apply raw args))
  (-direct [_ world] nil)
  (-describe [_] {:kind :lambda})
  clojure.lang.Fn
  clojure.lang.IFn
  (invoke [_] (complete (.invoke raw)))
  (invoke [_ a] (complete (.invoke raw a)))
  (invoke [_ a b] (complete (.invoke raw a b)))
  (invoke [_ a b c] (complete (.invoke raw a b c)))
  (invoke [_ a b c d] (complete (.invoke raw a b c d)))
  (invoke [_ a b c d e] (complete (.invoke raw a b c d e)))
  (invoke [_ a b c d e f] (complete (.invoke raw a b c d e f)))
  (invoke [_ a b c d e f g] (complete (.invoke raw a b c d e f g)))
  (invoke [_ a b c d e f g h] (complete (.invoke raw a b c d e f g h)))
  (applyTo [_ args] (complete (.applyTo raw args))))

(defn lambda [f] (Lambda. f))

(defn call
  "Call any function value from compiled code (L4.lower.calls): compiled
   callees directly, Klara closures in a nested machine, host functions as
   they are."
  [f args]
  (cond
    (instance? Lambda f) (apply (.-raw ^Lambda f) args)
    (instance? klara.runtime.value.IExecutable f)
    (let [^objects c (m/current-context)
          r (v/-call f (aget c 0) (aget c 1) (aget c 2) args)]
      (if (identical? r v/fallback) (nested f args) r))
    ;; a continuation resumes in the interpreter, in the caller's machine
    (instance? klara.runtime.value.Continuation f)
    (leave {:mode :apply :f f :args (mapv prims/freeze args)})
    (or (instance? Closure f) (m/intrinsic? f))
    (nested f args)
    ;; the same rule as the interpreter (L0.eval.not-fn)
    (not (instance? clojure.lang.IFn f))
    (fail :L0.eval.not-fn (str "cannot call " (pr-str f) ": not a function") :value (pr-str f))
    :else (apply f args)))

;; ---------------------------------------------------------------------------
;; Lowering

(def ^:private unsupported #{:interop :code :hole :def :letrec})

(defn- link-value [link]
  (case (:kind link)
    :pinned (klara.runtime.world/pin (:world link) (:name link))
    :guarded (:value link)
    nil))

(defn- loop-redex?
  "A call of a literal one-arity function, applied where it is made, whose
   body refers to itself only by recur: a loop."
  [t]
  (let [f (:fn t)]
    (and (= :fn (:op f)) (not (:recur t)) (:self f)
         (let [[a & more] (:arities f)]
           (and a (nil? more) (nil? (:rest a)) (= (count (:params a)) (count (:args t)))
                (not (contains? (t/free-locals (:body a)) (:self f)))
                (some #(and (= :recur (:op %)) (= (:self f) (:target %))) (t/nodes (:body a))))))))

(def ^:private array-hints
  {'booleans "[Z" 'bytes "[B" 'chars "[C" 'shorts "[S" 'ints "[I" 'longs "[J"
   'floats "[F" 'doubles "[D" 'objects "[Ljava.lang.Object;"})

(defn- hint-class
  "The class a host type hint names, or nil."
  ^Class [tag]
  (cond (class? tag) tag
        (contains? array-hints tag) (Class/forName (array-hints tag))
        (symbol? tag) (let [c (try (resolve tag) (catch Exception _ nil))] (when (class? c) c))
        (string? tag) (try (Class/forName tag) (catch Exception _ nil))
        :else nil))

(defn- may-leave?
  "Can evaluating `t` in compiled code produce a Leave? Host calls cannot:
   host code never sees one (see complete)."
  [t]
  (case (:op t)
    (:const :local :global :host :fn :recur :throw) false
    :app (let [f (:fn t)]
           (or (and (= :host (:op f)) (contains? leave-intrinsics (:name f)))
               (not (or (:recur t) (= :host (:op f))
                        (and (= :const (:op f)) (keyword? (:value f)))))))
    :if (or (boolean (:speculate t)) (boolean (some may-leave? (t/children t))))
    :let (or (some? (hint-class (:tag t))) (boolean (some may-leave? (t/children t))))
    (boolean (some may-leave? (t/children t)))))

(defn- inline-redex?
  "A call of a literal function with one fixed arity that does not refer to
   itself (by name or by recur; inner loops may recur to themselves),
   applied to as many arguments."
  [t]
  (let [f (:fn t)]
    (and (= :fn (:op f)) (not (:recur t))
         (let [[a & more] (:arities f)]
           (and a (nil? more) (nil? (:rest a)) (= (count (:params a)) (count (:args t)))
                (or (nil? (:self f)) (not (contains? (t/free-locals (:body a)) (:self f))))
                (not-any? #(and (= :recur (:op %)) (or (nil? (:target %)) (= (:self f) (:target %))))
                          (t/nodes (:body a))))))))

(defn- lower*
  "Lower term `t` with prepared node `n`. `scope` is the environment layout
   (names, as in klara.runtime.prepare); `frames` are the let contexts of the
   current function around this point, innermost first, each [body-node scope]."
  [t n scope frames consts self-name self-sym osr owned? entries]
  (let [selves (atom {})                 ; self name -> [fn node, free names]
        top t]
  (letfn [(constant [x]
            (let [i (count @consts)] (swap! consts conj x) (list 'clojure.core/nth 'consts i)))
          ;; a frame state's environment; a function's own name stands for the
          ;; interpreter's closure of it, so that the interpreter can recur
          (env-form [scope]
            (mapv (fn [nm]
                    (if-let [[fnode free] (get @selves nm)]
                      (list 'klara.compile.lower/interpreted (constant fnode) (vec free))
                      ;; owned values leave persistent (L4.check.in-place)
                      (list 'klara.runtime.prims/freeze nm)))
                  scope))
          (go [t n scope frames]
            (case (:op t)
              :const (let [x (:value t)]
                       (if (or (nil? x) (number? x) (string? x) (keyword? x) (boolean? x) (char? x))
                         x (constant x)))
              :local (:name t)
              :host (let [q (:name t)]
                      (cond (and (= "clojure.core" (namespace q)) (not (m/intrinsic? (m/host-value q)))) q
                            (:symbol (b/lookup q)) (:symbol (b/lookup q))
                            :else (constant (m/host-value q))))
              :global (let [l (:link t)]
                        (cond
                          ;; a recursive call of the definition being compiled: its own
                          ;; generation is a premise, so it denotes this function (L4.exec.valid)
                          (and (= :late (:kind l)) self-name (= (:name l) self-name)) self-sym
                          (= :late (:kind l))
                          (list 'klara.compile.lower/late (constant (Site. nil nil)) 'klara-ctx__ (list 'quote (:name l)))
                          :else (constant (link-value l))))
              :fn (let [^klara.runtime.prepare.Fn fnode n
                        self (or (:self t) (t/fresh "fn"))
                        free (:free t)
                        _ (swap! selves assoc self [fnode free])]
                    (as-> (list* 'fn* self
                           (mapv (fn [{:keys [params rest body]} ^klara.runtime.prepare.Arity a]
                                  (let [inner (cond-> (vec free)
                                                (.-self? a) (conj self)
                                                true (into params)
                                                rest (conj rest))]
                                    (list (cond-> (vec params) rest (conj '& rest))
                                          (list 'let* (cond-> entry-bindings
                                                        ;; L4.jit.trigger: a baseline candidate counts its entries
                                                        (and entries (identical? t top))
                                                        (into ['_ (list 'klara.compile.lower/count-entry! (constant entries))]))
                                                (list 'if tick-form
                                                      (list 'klara.compile.lower/leave-apply (constant fnode) (vec free)
                                                            (if rest (list 'clojure.core/into (vec params) rest) (vec params)))
                                                      (go body (.-body a) inner []))))))
                                (:arities t) (.-arities fnode))) form
                      ;; L4.exec.osr: an inner function can be entered from the
                      ;; interpreter given its captured values
                      (do (when (and (not (identical? t top))
                                     ;; it must not call the outer compiled function directly
                                     (not (some #{self-sym} (filter symbol? (tree-seq coll? seq form)))))
                            (swap! osr conj [fnode (list 'fn* (vec free) form)]))
                          ;; inner functions may reach host code (see Lambda)
                          (if (identical? t top) form (list 'klara.compile.lower/lambda form)))))
              :app (let [^klara.runtime.prepare.App an n
                         line (get-in t [:pos :line])
                         at (fn [form] (if (and line (seq? form)) (with-meta form {:line line}) form))
                         f (:fn t)
                         args (mapv (fn [x xn] (go x xn scope frames)) (:args t) (.-args an))]
                     (at (cond
                       (:recur t) (list* 'recur args)
                       ;; L4.check.in-place: own makes a transient only in code admitted as owned
                       (and (= :host (:op f)) (= 'klara.core/own (:name f)) (= 1 (count args)))
                       (if owned? (list 'klara.runtime.prims/owned (first args)) (first args))
                       ;; two-argument subtraction: the host picks a primitive overload
                       (and (= :host (:op f)) (= 'klara.core/- (:name f)) (= 2 (count args)))
                       (list* '.sub 'klara.runtime.prims/SUB args)
                       ;; ((fn loop [p ..] body) a ..) with recur: a host loop, so the
                       ;; host can keep its locals primitive (L4.lower.steps: one step
                       ;; per iteration, as before)
                       (loop-redex? t)
                       (let [^klara.runtime.prepare.Fn fnode (.-f an)
                             self (:self f)
                             {:keys [params body]} (first (:arities f))
                             ^klara.runtime.prepare.Arity a (first (.-arities fnode))
                             free (:free f)
                             _ (swap! selves assoc self [fnode free])
                             inner (cond-> (vec free) (.-self? a) (conj self) true (into params))
                             leave-form (list 'klara.compile.lower/leave-apply (constant fnode) (vec free) (vec params))
                             body-form (go body (.-body a) inner [])
                             step (list 'if tick-form leave-form body-form)
                             tmps (mapv (fn [_] (t/fresh "arg")) params)]
                         ;; L4.exec.osr: the same loop as a function, for re-entry
                         (when-not (some #{self-sym} (filter symbol? (tree-seq coll? seq body-form)))
                           (swap! osr conj [fnode (list 'fn* (vec free) (list 'fn* self (list (vec params) (list 'let* entry-bindings step))))]))
                         (list 'let* (vec (interleave tmps args))
                               (list 'loop* (vec (interleave params tmps)) step)))
                       ;; ((fn [p ..] body) a ..): the call happens in place, as a let
                       ;; with the function's entry step and frame state (L4.lower.steps)
                       (inline-redex? t)
                       (let [^klara.runtime.prepare.Fn fnode (.-f an)
                             {:keys [params body]} (first (:arities f))
                             ^klara.runtime.prepare.Arity a (first (.-arities fnode))
                             free (:free f)]
                         ;; application binds in parallel: arguments go to fresh
                         ;; temporaries first, since they may mention the parameter
                         ;; names (an inlined function called with its own locals)
                         (list 'let* (let [tmps (mapv (fn [_] (t/fresh "arg")) params)]
                                                (into (vec (interleave tmps args)) (interleave params tmps)))
                                        (list 'if tick-form
                                              (list 'klara.compile.lower/leave-apply (constant fnode) (vec free) (vec params))
                                              (go body (.-body a) (into (vec free) params) []))))
                       ;; L4.exec.leave: perform and handle are applied by the interpreter
                       (and (= :host (:op f)) (contains? leave-intrinsics (:name f)))
                       (list 'klara.compile.lower/leave-intrinsic (constant (m/host-value (:name f))) (vec args))
                       (and (= :host (:op f)) (= 'clojure.core/aget (:name f)) (= 2 (count args)))
                       (list* 'klara.compile.lower/array-get args)
                       (and (= :host (:op f)) (= 'clojure.core/alength (:name f)) (= 1 (count args)))
                       (list* 'klara.compile.lower/array-length args)
                       (and (= :host (:op f)) (= "clojure.core" (namespace (:name f)))
                            (not (m/intrinsic? (m/host-value (:name f)))))
                       (list* (:name f) args)
                       (and (= :host (:op f)) (:symbol (b/lookup (:name f))))
                       (list* (:symbol (b/lookup (:name f))) args)
                       ;; account operations on the context's wallet (L4.check.affine-erase)
                       (and (= :host (:op f)) (contains? acct/compiled (:name f)))
                       (list* (acct/compiled (:name f)) args)
                       (and self-name (= :global (:op f)) (= :late (get-in f [:link :kind])) (= self-name (get-in f [:link :name])))
                       (list* self-sym args)
                       ;; (:k m) and (:k m default): keyword lookup, as the host does it
                       ;; (L0.eval.not-fn: applying a keyword is get)
                       (and (= :const (:op f)) (keyword? (:value f)) (<= 1 (count args) 2))
                       (list* (:value f) args)
                       ;; a call of a late definition: directly when the callee is
                       ;; compiled and holds here (L4.lower.direct), else as any call
                       (and (= :global (:op f)) (= :late (get-in f [:link :kind])))
                       (let [site (constant (Site. nil nil))
                             q (list 'quote (get-in f [:link :name]))
                             d (t/fresh "direct")]
                         (list 'let* [d (list 'klara.compile.lower/direct site 'klara-ctx__ q)]
                                        (list 'if d
                                              (list* '.invoke (with-meta d {:tag 'clojure.lang.IFn}) args)
                                              (list 'klara.compile.lower/call (list 'klara.compile.lower/late site 'klara-ctx__ q) (vec args)))))
                       :else (list 'klara.compile.lower/call (go f (.-f an) scope frames) (vec args)))))
              :recur (let [^klara.runtime.prepare.Recur rn n]
                       (list* 'recur (mapv (fn [x xn] (go x xn scope frames)) (:args t) (.-args rn))))
              :let (let [^klara.runtime.prepare.Let ln n
                         x (:name t)
                         inner (conj scope x)
                         hint (hint-class (:tag t))
                         body (go (:body t) (.-body ln) inner frames)
                         ;; L4.lower.hint: a hint is a guard; where it does not hold the
                         ;; interpreter goes on with the body
                         body (if hint
                                (list 'if (list '.isInstance (with-meta (constant hint) {:tag 'java.lang.Class}) x)
                                      (list 'let* [(with-meta x {:tag (if (contains? array-hints (:tag t)) (:tag t) (symbol (.getName hint)))}) x]
                                            body)
                                      (list 'klara.compile.lower/leave-eval (constant (.-body ln)) (env-form inner)))
                                body)]
                     (list 'let* [x (go (:init t) (.-init ln) scope (cons [(.-body ln) scope] frames))]
                           (if (may-leave? (:init t))
                             ;; L4.exec.frame-state: a Leave passing out adds this let's frame
                             (list 'if (list 'clojure.core/instance? 'klara.compile.lower.Leave x)
                                   (list 'klara.compile.lower/leave-up x
                                         (list 'klara.compile.lower/let-frame (constant (.-body ln)) (env-form scope)))
                                   body)
                             body)))
              :if (let [^klara.runtime.prepare.If in n]
                    (list 'if (go (:test t) (.-test in) scope frames)
                          (go (:then t) (.-then in) scope frames)
                          (if (:speculate t)
                            ;; L4.exec.leave: the else branch of a speculation is the reference
                            (list 'klara.compile.lower/leave-eval (constant (.-else in)) (env-form scope))
                            (go (:else t) (.-else in) scope frames))))
              :throw (list 'throw (go (:ex t) (.-ex ^klara.runtime.prepare.Throw n) scope frames))
              ;; L4.lower.try
              :try (let [^klara.runtime.prepare.Try tn n
                         fin-n (.-finally tn)
                         env (env-form scope)
                         v (t/fresh "v")
                         passing (fn [form frame]
                                   (list 'let* [v form]
                                         (list 'if (list 'clojure.core/instance? 'klara.compile.lower.Leave v)
                                               (list 'klara.compile.lower/leave-up v frame) v)))
                         body (passing (go (:body t) (.-body tn) scope frames)
                                       (list 'klara.compile.lower/try-frame (constant (.-catches tn)) (constant fin-n)
                                             env 'klara-ctx__))
                         arms (map (fn [c cn]
                                     (let [x (:name c)
                                           h (go (:body c) (:body cn) (conj scope x) frames)]
                                       (list 'catch (symbol (.getName ^Class (:class cn))) x
                                             (if fin-n
                                               (passing h (list 'klara.compile.lower/finally-frame (constant fin-n) env))
                                               h))))
                                   (:catches t) (.-catches tn))
                         inner (list* 'try body arms)]
                     (if-let [f (:finally t)]
                       (let [fin (go f fin-n scope frames)
                             r (t/fresh "try")
                             ex (t/fresh "ex")]
                         (list 'let* [r (list 'try inner (list 'catch 'java.lang.Throwable ex (list 'do fin (list 'throw ex))))]
                               (list 'if (list 'clojure.core/instance? 'klara.compile.lower.Leave r) r (list 'do fin r))))
                       inner))
              (fail :L4.lower.subset (str "the backend does not compile " (:op t)))))]
    (go t n scope frames))))

(defn- compiled-nodes
  "The nodes lowering compiles: the else branch of a speculation is left to
   the interpreter (L4.exec.leave), so it need not be compilable."
  [term]
  (tree-seq (comp seq t/children)
            (fn [n] (if (and (= :if (:op n)) (:speculate n)) [(:test n) (:then n)] (t/children n)))
            term))

(defn mint-safe?                                         ; L4.exec.mint-safe
  "Does compiled code for `term` create no closures that outlive the call?
   Then it may run under a mint (L1.context.mint): its only inner functions
   are applied where they are made (loops, inlined calls)."
  [term]
  (let [applied (into #{} (comp (filter #(= :app (:op %))) (map :fn) (filter #(= :fn (:op %))) (map t/->form))
                      (compiled-nodes term))]
    (every? #(contains? applied (t/->form %))
            (filter #(= :fn (:op %)) (rest (compiled-nodes term))))))

(defn- recur-inside?
  "Does `t` contain a recur that is not inside a function of its own?"
  [t]
  (case (:op t)
    :recur true
    :fn false
    (boolean (some recur-inside? (t/children t)))))

(defn subset-violation
  "The first construct outside the compilable subset (L4.lower.subset), or nil."
  [term]
  (some (fn [n]
          (cond (contains? unsupported (:op n)) (:op n)
                (and (= :host (:op n)) (m/intrinsic? (m/host-value (:name n)))
                     (not (contains? acct/compiled (:name n)))
                     (not (contains? leave-intrinsics (:name n))))
                (:name n)
                ;; L4.lower.try: the host does not recur across a try, and a finally
                ;; clause runs in compiled code only where it cannot leave
                (and (= :try (:op n)) (recur-inside? n)) "recur inside try"
                (and (= :try (:op n)) (:finally n) (may-leave? (:finally n))) "a finally clause that may leave"))
        (compiled-nodes term)))

(defn lower
  "Compile a :fn term to a host function. With :self-name, late references
   to that definition call the compiled function itself. With :owned?, the
   term was admitted as owned (L4.check.in-place) and `own` makes transients.
   With :entries (a long array), the function counts its entries in it."
  ([term] (lower term {}))
  ([term {:keys [self-name owned? entries]}]
   (when-not (= :fn (:op term)) (fail :L4.lower.subset "only functions are compiled"))
   (when-let [x (subset-violation term)]
     (fail :L4.lower.subset (str "the backend does not compile " x)))
   (let [consts (atom [])
         file (some #(get-in % [:pos :file]) (t/nodes term))
         self-sym (or (:self term) (t/fresh "self"))
         term (anf/anf (assoc term :self self-sym))
         node (m/prepare-term term)
         osr (atom [])
         form (lower* term node [] () consts self-name self-sym osr (boolean owned?) entries)
         osr-entries @osr
         wrapper (list 'fn* ['consts] (vector form (mapv second osr-entries)))
         [f factories] ((with-bindings {#'*ns* (the-ns 'klara.compile.lower)
                                        clojure.lang.Compiler/SOURCE_PATH (or file "klara")
                                        clojure.lang.Compiler/SOURCE (if file (.getName (java.io.File. ^String file)) "klara")}
                          (eval wrapper))
                        @consts)]
     {:form form
      :anf term
      ;; compiled code reports the Klara source file and lines (L0.trace.positions)
      :fn f
      ;; [fn-node factory]: factory of captured values -> compiled function
      :osr (mapv (fn [[fnode _] factory] [fnode factory]) osr-entries factories)})))
