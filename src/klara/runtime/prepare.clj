(ns klara.runtime.prepare
  "Prepared nodes: the machine's executable form of Core terms.

  Core terms (klara.lang.term) remain the canonical representation: the
  checker, reify, lowering and the formal bridge read them. Before the CEK
  machine evaluates a term it prepares it once into nodes, which differ only
  in representation:

  - locals are slots in a vector environment, computed from scope;
  - host functions are resolved;
  - calls of host functions on immediate arguments are marked `flat`;
  - each global keeps an inline cache keyed by world identity (worlds are
    immutable, so a cached resolution stays valid for that world).

  Environment layout of a function body: captured free locals in the order
  of the term's :free, then the function itself if its body refers to it,
  then the parameters, then the rest parameter. let, letrec, catch and code
  holes push further slots. Frames hold persistent vectors, so captured
  continuations stay multi-shot."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]))

(set! *warn-on-reflection* true)

(definterface INode (^long tag []) (sourceTerm []))

(defmacro ^:private defnode
  "A node type with a constant tag and the original term for inspection."
  [name tag fields]
  `(deftype ~name ~(into ['term] fields)
     INode (~'tag [_#] ~tag) (~'sourceTerm [_#] ~'term)
     Object (~'toString [_#] (str "#node" ~(str "/" name)))))

(def ^:const CONST 0) (def ^:const LOCAL 1) (def ^:const GLOBAL 2) (def ^:const HOST 3)
(def ^:const FN 4) (def ^:const APP 5) (def ^:const LET 6) (def ^:const LETREC 7)
(def ^:const IF 8) (def ^:const DO 9) (def ^:const RECUR 10) (def ^:const THROW 11)
(def ^:const TRY 12) (def ^:const INTEROP 13) (def ^:const DEF 14) (def ^:const CODE 15)

(defnode Const 0 [value])
(defnode Local 1 [^long slot name])
;; A global keeps the world identity, dispatch epoch and value of its last
;; late resolution (worlds are immutable, so the value stays valid for that
;; world). It keeps the world's id, not the world: a cache must not be a root
;; (L1.retain.roots).
(definterface IGlobalCache
  (cached [id ^long epoch])
  (cache [id ^long epoch value]))

;; One immutable entry per cache, replaced as a whole: jobs run in parallel
;; on different worlds (L3.job.parallel), so a world id and its value must
;; never be read from two different writes.
(deftype CacheEntry [id ^long epoch value])

(defn entry-value
  "The value cached in `e` for world `id` at dispatch `epoch`, or nil."
  [^CacheEntry e id ^long epoch]
  (when (and e (identical? (.-id e) id) (== (.-epoch e) epoch)) (.-value e)))

(deftype Global [term link ^:volatile-mutable entry]
  INode (tag [_] 2) (sourceTerm [_] term)
  IGlobalCache
  (cached [_ id epoch] (entry-value entry id epoch))
  (cache [_ id epoch value] (set! entry (CacheEntry. id epoch value)) value)
  Object (toString [_] "#node/Global"))
(defnode Host 3 [value name])
;; arities: vector of Arity; captured: slots of the free locals in the enclosing scope
(definterface IOsr
  (osr [])
  (setOsr [entry]))

;; A function node. `osr` is set when compiled code for this very node
;; exists (it belongs to a candidate whose leaves continue here): an IFn of
;; [closure world mint] returning an executable for the closure, or nil.
(deftype Fn [term arities captured profile ^:volatile-mutable osr-entry]
  INode (tag [_] 4) (sourceTerm [_] term)
  IOsr (osr [_] osr-entry) (setOsr [_ e] (set! osr-entry e))
  Object (toString [_] "#node/Fn"))
(defnode App 5 [f args flat recur-arity all-imm profile self-call])
(defnode Let 6 [init body])
(defnode Letrec 7 [fns body])
(defnode If 8 [test then else profile])
(defnode Do 9 [exprs last])
(defnode Recur 10 [^long slot ^long arity args all-imm])
(defnode Throw 11 [ex])
(defnode Try 12 [body catches finally])
(defnode Interop 13 [args])
(defnode Def 14 [init])
;; free-slots: [name slot] for the template's present-stage locals;
;; binders: template binder names, in the order holes see them as slots
(defnode Code 15 [free-slots binders holes])

(deftype Arity [^long nparams rest? self? body])

(defn tag ^long [^INode n] (.tag n))

;; ---------------------------------------------------------------------------
;; Profiles (spec/L4-compiler.md#profiles, design/06-speculation.md#5-profiles)
;;
;; Mutable feedback owned by a node, written by the interpreter and read by
;; Klara as data. An observation that matches what was seen before writes
;; nothing, so a monomorphic program pays only a comparison.

(definterface IProfile
  (enter [args external]) ; a function entry with its arguments; external: not a self call
  (call [callee])         ; a call node evaluated with this callee
  (branch [taken])        ; an if node took its then (true) or else branch
  (snapshot []))

(def ^:private poly ::polymorphic)
(def ^:private unstable ::unstable)

(defn- cheap-value?
  "Values compared by equality; others are tracked by identity, weakly, so a
   profile never keeps a large argument alive (L1.retain.roots)."
  [x]
  (or (nil? x) (keyword? x) (string? x) (number? x) (boolean? x) (symbol? x) (char? x)))

(defn- observe-value [x]
  (if (cheap-value? x) x (java.lang.ref.WeakReference. x)))

(defn- observed [v]
  (if (instance? java.lang.ref.Reference v) (.get ^java.lang.ref.Reference v) v))

(defn- plain-size
  "The number of scalars in x if it is plain data (scalars and collections of
   plain data, nothing that could keep a world, a function or a mutable
   object alive) of at most `bound` of them, else nil."
  [x ^long bound]
  (let [n (volatile! 0)]
    (letfn [(walk [x]
              (cond (cheap-value? x) (<= (vswap! n inc) bound)
                    (and (coll? x) (not (instance? clojure.lang.LazySeq x)))
                    (every? walk (if (map? x) (mapcat identity x) x))
                    :else false))]
      (when (walk x) @n))))

(defn- sample-of
  "Arguments kept as a sample (L1.retain.roots): held strongly when they are
   plain data of at most 10000 scalars in all, so a profile keeps at most one
   bounded sample per function and never a world, a function or a mutable
   object; otherwise only weakly."
  [args]
  (if (plain-size args 10000)
    args
    (java.lang.ref.WeakReference. args)))

(defn- same-observation? [v x]
  (if (instance? java.lang.ref.WeakReference v)
    (identical? (.get ^java.lang.ref.WeakReference v) x)
    (and (cheap-value? x) (= v x) (= (class v) (class x)))))

(deftype Profile [^:volatile-mutable ^long n
                  ^:volatile-mutable ^long external-n            ; entries other than self calls
                  ^:volatile-mutable ^objects classes   ; per argument: a class, or poly
                  ^:volatile-mutable ^objects values    ; per argument: a value, or unstable
                  ^:volatile-mutable callee
                  ^:volatile-mutable ^long taken
                  ^:volatile-mutable ^long not-taken
                  ^:volatile-mutable sample]                   ; recent arguments (see sample-of)
  IProfile
  (enter [_ args external]
    (set! n (inc n))
    (when external
      (set! external-n (inc external-n))
      (when (zero? (bit-and external-n (dec external-n)))     ; at counts 1, 2, 4, 8, ...
        (set! sample (sample-of args))))
    (let [cnt (count args)]
     (when external
      (if (nil? classes)
        (do (set! classes (object-array (map class args)))
            (set! values (object-array (map observe-value args))))
        (when (== cnt (alength classes))
          (dotimes [i cnt]
            (let [x (nth args i) c (aget classes i)]
              (when (and (not (identical? c poly)) (not (identical? c (class x))))
                (aset classes i poly))
              (let [v (aget values i)]
                (when-not (or (identical? v unstable) (same-observation? v x))
                  (aset values i unstable))))))))))
  (call [_ f]
    (set! n (inc n))
    (cond (nil? callee) (set! callee f)
          (and (not (identical? callee poly)) (not (identical? callee f))) (set! callee poly)))
  (branch [_ t]
    (if t (set! taken (inc taken)) (set! not-taken (inc not-taken))))
  (snapshot [_]
    {:count n
     :external external-n
     :classes (when classes (mapv #(if (identical? % poly) :polymorphic %) classes))
     :stable (when values (mapv #(if (identical? % unstable) :unstable [:value (observed %)]) values))
     :callee (cond (nil? callee) nil (identical? callee poly) :polymorphic :else callee)
     :branches [taken not-taken]
     :sample (observed sample)}))

(defn new-profile [] (Profile. 0 0 nil nil nil 0 0 nil))

(defonce ^{:doc "Whether the interpreter records profiles (L4.profile.record)."} profiling (atom true))

;; Cache access for globals (the machine is the only writer).
(defn global-cached [^IGlobalCache g id ^long epoch] (.cached g id epoch))
(defn global-cache! [^IGlobalCache g id ^long epoch value] (.cache g id epoch value))

;; ---------------------------------------------------------------------------
;; Preparation

(declare prep)

(defn- slot-of [scope name]
  (let [i (.lastIndexOf ^java.util.List scope name)]
    (when (neg? i) (throw (ex-info (str "unbound local " name) {:rule :L0.term.wf :name name})))
    i))

(defn- immediate? [t]
  (contains? #{:const :local :global :host} (:op t)))

(defn imm-node?
  "Is prepared node `n` evaluated without a frame (see the machine's imm)?"
  [n]
  (let [tg (tag n)]
    (or (<= tg 4) (and (== tg 5) (.-flat ^App n)))))

(defn- self-used? [self arity]
  (and self (or (contains? (t/free-locals (:body arity)) self)
                (some #(and (= :recur (:op %)) (= self (:target %))) (t/nodes (:body arity))))))

(defn prep-fn [scope term host-value]
  (let [free (:free term)
        self (:self term)]
    (Fn. term
         (mapv (fn [a]
                 (let [used (boolean (self-used? self a))
                       inner (cond-> (vec free)
                               used (conj self)
                               true (into (:params a))
                               (:rest a) (conj (:rest a)))]
                   (Arity. (count (:params a)) (boolean (:rest a)) used (prep inner (:body a) host-value))))
               (:arities term))
         (mapv #(slot-of scope %) free)
         (new-profile)
         nil)))

(defn prep
  "Prepare term `t` in `scope` (a vector of local names, index = slot).
   `host-value` resolves a host function name."
  [scope t host-value]
  (let [go #(prep scope % host-value)]
    (case (:op t)
      :const (Const. t (:value t))
      :local (Local. t (slot-of scope (:name t)) (:name t))
      :global (Global. t (:link t) nil)
      :host (Host. t (host-value (:name t)) (:name t))
      :fn (prep-fn scope t host-value)
      :app (let [f (:fn t)
                 hv (when (= :host (:op f)) (host-value (:name f)))
                 flat (and (= :host (:op f)) (not (:recur t))
                           (not (instance? clojure.lang.IRecord hv)) ; intrinsics are records
                           (every? immediate? (:args t)))]
             (let [args (mapv go (:args t))]
               (App. t (go f) args flat (:recur t) (every? imm-node? args) (new-profile) (boolean (:self-call t)))))
      :let (Let. t (go (:init t)) (prep (conj scope (:name t)) (:body t) host-value))
      :letrec (let [names (mapv first (:bindings t))
                    inner (into scope names)]
                (Letrec. t (mapv #(prep-fn inner (second %) host-value) (:bindings t))
                         (prep inner (:body t) host-value)))
      :if (If. t (go (:test t)) (go (:then t)) (go (:else t)) (new-profile))
      :do (Do. t (mapv go (butlast (:body t))) (go (last (:body t))))
      :recur (let [args (mapv go (:args t))]
               (Recur. t (slot-of scope (:target t)) (:arity t) args (every? imm-node? args)))
      :throw (Throw. t (go (:ex t)))
      :try (Try. t (go (:body t))
                 (mapv (fn [c] {:class (:class c) :body (prep (conj scope (:name c)) (:body c) host-value)})
                       (:catches t))
                 (some-> (:finally t) go))
      :interop (Interop. t (mapv go (t/children t)))
      :def (Def. t (go (:init t)))
      :code (let [binders (vec (sort (into #{} (mapcat t/binders) (t/nodes (:template t)))))
                  hole-scope (into scope binders)]
              (Code. t (mapv (fn [n] [n (slot-of scope n)]) (:free t)) binders
                     (mapv #(prep hole-scope % host-value) (:holes t))))
      (throw (ex-info (str "cannot prepare " (:op t)) {:rule :L0.term.wf :op (:op t)})))))
