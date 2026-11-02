(ns klara.runtime.value
  "Runtime values (spec/L0-core.md#values): closures, continuations, Code,
  worlds and definitions.

  Closures and continuations implement IFn so host code (clojure.core/map,
  sort-by, ...) can call them; such calls run a nested machine
  (L3.effect.host-boundary). The machine installs that entry point in
  `host-invoke` when it loads, which avoids a namespace cycle."
  (:require [klara.lang.term :as t]))

(set! *warn-on-reflection* true)

(defprotocol IExecutable
  "A compiled implementation (L4): the machine calls -execute with its state
   and the arguments, and gets a new state back. Compiled code calls -call
   with the current context and gets the value, or `fallback` when the
   candidate is not valid there."
  (-execute [f st args])
  (-call [f world mint dyn args])
  (-direct [f world]
    "The host function to call directly in `world` without a mint, when it
     needs no check at the call (valid there, no argument guards); else nil.")
  (-describe [f]))

(def fallback ::fallback)

(defonce host-invoke (atom (fn [f args] (throw (ex-info "machine not loaded" {})))))

(defn- callable-methods
  "IFn methods (arities 0..20 and applyTo) delegating to host-invoke."
  []
  (let [this (gensym "this")
        rest-sym (gensym "args")]
    (concat (for [n (range 21)]
              (let [args (vec (repeatedly n #(gensym "a")))]
                `(~'invoke [~this ~@args] (@host-invoke ~this ~args))))
            [`(~'applyTo [~this ~rest-sym] (@host-invoke ~this (vec ~rest-sym)))])))

(defmacro deftype-callable
  "deftype that host code can call: its IFn methods delegate to host-invoke."
  [name fields & specs]
  `(deftype ~name ~fields clojure.lang.Fn clojure.lang.IFn ~@(callable-methods) ~@specs))

(defmacro defrecord-callable
  "defrecord that host code can call, as deftype-callable."
  [name fields & specs]
  `(defrecord ~name ~fields clojure.lang.IFn ~@(callable-methods) ~@specs))

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

;; term: a :fn Core term; node: its prepared form (klara.runtime.prepare);
;; env: vector of the captured values of (:free term), in that order;
;; basis: nil (open) or a World (L1.context.mint)
(deftype-callable Closure [term node env basis]
  Object
  (toString [_] (str "#klara/fn[" (or (some-> (:self term) t/base-name) "anonymous")
                     (when basis (str " @" (.-id ^World basis))) "]")))

(defmethod print-method Closure [c ^java.io.Writer out] (.write out (str c)))

(defn closure? [x] (instance? Closure x))

(defn rebase
  "A closure with basis `w` if it has none (L1.context.get)."
  [x w]
  (if (and (closure? x) (nil? (.-basis ^Closure x)))
    (Closure. (.-term ^Closure x) (.-node ^Closure x) (.-env ^Closure x) w)
    x))

(defn captured
  "The captured locals of closure `c` as a map from name to value."
  [^Closure c]
  (zipmap (:free (.-term c)) (.-env c)))

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
;; Account tokens (L3.account.token): identity only; what a token holds is
;; kept by the wallet it was taken from (klara.runtime.account).

(deftype Token [owner]
  Object
  (toString [_] (str "#klara/token " owner)))

(defmethod print-method Token [t ^java.io.Writer out] (.write out (str t)))

;; ---------------------------------------------------------------------------
;; Mutability (L2.lift.mutable, L3.job.host-mutation)

(defn mutable? [x]
  (and (some? x)
   (or (instance? clojure.lang.IAtom x) (instance? clojure.lang.Volatile x)
      (instance? Token x)
      (instance? clojure.lang.IRef x) (.isArray (class x))
      ;; a host transient: writable in place by whoever holds it
      (instance? clojure.lang.ITransientCollection x)
      (and (instance? java.util.Collection x) (not (instance? clojure.lang.IPersistentCollection x)))
      (and (instance? java.util.Map x) (not (instance? clojure.lang.IPersistentMap x))))))

(defonce ^:private pure-objects
  (java.util.Collections/synchronizedSet (java.util.Collections/newSetFromMap (java.util.WeakHashMap.))))

(defn declare-pure!
  "Declare host function object f pure (a record constructor): pure code may
   call a definition holding it (L4.facts.pure). Weak: f is not kept alive."
  [f]
  (.add ^java.util.Set pure-objects f)
  f)

(defn declared-pure? [f] (.contains ^java.util.Set pure-objects f))

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

(defn data?
  "Immutable data: collections of data, keywords and symbols (IFn on the JVM,
   values in Klara) and other values that are neither functions nor mutable.
   The checker computes with it (L4.check.prim, L4.check.delta-data)."
  [x]
  (cond (or (keyword? x) (symbol? x)) true
        (coll? x) (and (not (instance? clojure.lang.LazySeq x)) (not (record? x))
                       (every? data? (if (map? x) (mapcat identity x) x)))
        :else (not (or (fn? x) (closure? x) (instance? clojure.lang.IFn x) (mutable? x)))))
