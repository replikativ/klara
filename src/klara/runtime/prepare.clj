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

(deftype Global [term link ^:volatile-mutable cid ^:volatile-mutable ^long cepoch ^:volatile-mutable cvalue]
  INode (tag [_] 2) (sourceTerm [_] term)
  IGlobalCache
  (cached [_ id epoch] (when (and (identical? cid id) (== cepoch epoch)) cvalue))
  (cache [_ id epoch value] (set! cid id) (set! cepoch epoch) (set! cvalue value) value)
  Object (toString [_] "#node/Global"))
(defnode Host 3 [value name])
;; arities: vector of Arity; captured: slots of the free locals in the enclosing scope
(defnode Fn 4 [arities captured])
(defnode App 5 [f args flat recur-arity all-imm])
(defnode Let 6 [init body])
(defnode Letrec 7 [fns body])
(defnode If 8 [test then else])
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
         (mapv #(slot-of scope %) free))))

(defn prep
  "Prepare term `t` in `scope` (a vector of local names, index = slot).
   `host-value` resolves a host function name."
  [scope t host-value]
  (let [go #(prep scope % host-value)]
    (case (:op t)
      :const (Const. t (:value t))
      :local (Local. t (slot-of scope (:name t)) (:name t))
      :global (Global. t (:link t) nil -1 nil)
      :host (Host. t (host-value (:name t)) (:name t))
      :fn (prep-fn scope t host-value)
      :app (let [f (:fn t)
                 hv (when (= :host (:op f)) (host-value (:name f)))
                 flat (and (= :host (:op f)) (not (:recur t))
                           (not (instance? clojure.lang.IRecord hv)) ; intrinsics are records
                           (every? immediate? (:args t)))]
             (let [args (mapv go (:args t))]
               (App. t (go f) args flat (:recur t) (every? imm-node? args))))
      :let (Let. t (go (:init t)) (prep (conj scope (:name t)) (:body t) host-value))
      :letrec (let [names (mapv first (:bindings t))
                    inner (into scope names)]
                (Letrec. t (mapv #(prep-fn inner (second %) host-value) (:bindings t))
                         (prep inner (:body t) host-value)))
      :if (If. t (go (:test t)) (go (:then t)) (go (:else t)))
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
