(ns klara.runtime.value
  "Runtime values (spec/L0-core.md#values): closures, continuations, Code,
  worlds and definitions.

  Closures and continuations implement IFn so host code (clojure.core/map,
  sort-by, ...) can call them; such calls run a nested machine
  (L3.effect.host-boundary). The machine installs that entry point in
  `host-invoke` when it loads, which avoids a namespace cycle."
  (:require [klara.lang.term :as t]))

(defprotocol IExecutable
  "A compiled implementation (L4): the machine calls -execute with its state
   and the arguments, and gets a new state back."
  (-execute [f st args])
  (-describe [f]))

(defonce host-invoke (atom (fn [f args] (throw (ex-info "machine not loaded" {})))))

(defmacro deftype-callable
  "deftype whose IFn methods (arities 0..20 and applyTo) delegate to host-invoke."
  [name fields & specs]
  (let [this (gensym "this")
        sigs (for [n (range 21)]
               (let [args (vec (repeatedly n #(gensym "a")))]
                 `(~'invoke [~this ~@args] (@host-invoke ~this ~args))))
        rest-sym (gensym "args")]
    `(deftype ~name ~fields
       clojure.lang.Fn
       clojure.lang.IFn
       ~@sigs
       (~'applyTo [~this ~rest-sym] (@host-invoke ~this (vec ~rest-sym)))
       ~@specs)))

;; ---------------------------------------------------------------------------
;; World and definitions (spec/L1-worlds.md)

(defrecord Definition [name form term value generation reads macro?])

(deftype World [id parent defs namespaces footprint delta]
  ;; footprint: nil for a whole world; a set of names for a slice (L1.slice.*)
  ;; delta: changes since the world this one was forked or published from
  Object
  (equals [_ o] (and (instance? World o) (= id (.-id ^World o))))
  (hashCode [_] (hash id))
  (toString [_] (str "#klara/world " id (when footprint " (slice)"))))

(defmethod print-method World [w ^java.io.Writer out] (.write out (str w)))

(defn world? [x] (instance? World x))

;; ---------------------------------------------------------------------------
;; Closures

;; term: a :fn Core term; env: {name value} for exactly (:free term);
;; basis: nil (open) or a World (L1.context.mint)
(deftype-callable Closure [term env basis]
  Object
  (toString [_] (str "#klara/fn[" (or (some-> (:self term) t/base-name) "anonymous")
                     (when basis (str " @" (.-id ^World basis))) "]")))

(defmethod print-method Closure [c ^java.io.Writer out] (.write out (str c)))

(defn closure? [x] (instance? Closure x))

(defn rebase
  "A closure with basis `w` if it has none (L1.context.get)."
  [x w]
  (if (and (closure? x) (nil? (.-basis ^Closure x)))
    (Closure. (.-term ^Closure x) (.-env ^Closure x) w)
    x))

;; ---------------------------------------------------------------------------
;; Continuations (spec/L3-effects.md)

(deftype-callable Continuation [frames world mint]
  Object
  (toString [_] (str "#klara/cont[" (count frames) " frames]")))

(defmethod print-method Continuation [c ^java.io.Writer out] (.write out (str c)))

;; ---------------------------------------------------------------------------
;; Code (spec/L2-staging.md)

(declare code-form)

(deftype Code [term]
  Object
  (equals [_ o] (and (instance? Code o) (= term (.-term ^Code o))))
  (hashCode [_] (hash term))
  (toString [this] (str "#klara/code " (pr-str (code-form this)))))

(defn code? [x] (instance? Code x))

(defn code-form [^Code c]
  (binding [t/*world-name* (fn [w] (if (world? w) (.-id ^World w) (str w)))]
    (t/->form (.-term c))))

(defmethod print-method Code [c ^java.io.Writer out] (.write out (str c)))

;; A future-stage variable during code construction (L2.code.build).
(defrecord CodeVar [name])

;; ---------------------------------------------------------------------------
;; Mutability (L2.lift.mutable, L3.job.host-mutation)

(defn mutable? [x]
  (and (some? x)
   (or (instance? clojure.lang.IAtom x) (instance? clojure.lang.Volatile x)
      (instance? clojure.lang.IRef x) (.isArray (class x))
      (and (instance? java.util.Collection x) (not (instance? clojure.lang.IPersistentCollection x)))
      (and (instance? java.util.Map x) (not (instance? clojure.lang.IPersistentMap x))))))

(defn find-mutable
  "The first mutable object reachable through immutable data, or nil."
  [x]
  (cond
    (or (nil? x) (string? x) (number? x) (keyword? x) (symbol? x) (boolean? x) (char? x)) nil
    (or (closure? x) (code? x) (world? x) (instance? Continuation x) (fn? x) (class? x)) nil
    (or (vector? x) (map? x) (set? x) (instance? clojure.lang.PersistentList x))
    (some find-mutable (if (map? x) (mapcat identity x) x))
    (instance? clojure.lang.IPersistentCollection x) nil   ; lazy or other seqs: not traversed
    (mutable? x) x
    :else nil))
