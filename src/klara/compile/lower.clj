(ns klara.compile.lower
  "The backend (spec/L4-compiler.md#lowering): checked Core terms to JVM
  classes through the Clojure compiler.

  A lowered function is a host fn. Late links are looked up in the
  effective world of the call (L4.lower.links), read from the machine's
  current context (klara.runtime.machine/current-context). Calls to Klara closures run in a
  nested machine whose effects abandon the compiled call (L4.lower.calls,
  L4.exec.deopt). Each lowering is compiled by `eval`, which uses a fresh
  class loader (L4.retain.classes)."
  (:require [klara.lang.term :as t]
            [klara.runtime.machine :as m]
            [klara.runtime.value :as v])
  (:import [klara.runtime.value Closure]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; ---------------------------------------------------------------------------
;; Runtime support called from lowered code

(defn tick!
  "L4.lower.steps: one step per function entry and loop iteration."
  []
  (let [^objects c (m/current-context)]
    (when-let [^longs meter (:meter (aget c 2))]
      (aset meter 0 (dec (aget meter 0)))
      (when (neg? (aget meter 0)) (m/abandon! :exhausted)))))

;; A call site of a late link: the world id, dispatch epoch and value of its
;; last resolution, as in the interpreter's globals (klara.runtime.prepare).
(definterface ISite (lookup [q]))

(deftype Site [^:volatile-mutable cid ^:volatile-mutable ^long cepoch ^:volatile-mutable cvalue]
  ISite
  (lookup [_ q]
    (let [^objects c (m/current-context)
          world (aget c 0)
          id (.-id ^klara.runtime.value.World world)
          epoch (.get m/dispatch-epoch)]
      (if (and (identical? cid id) (== cepoch epoch))
        cvalue
        (let [x (m/resolve-link {:kind :late :name q} world (:session (aget c 2)))]
          (set! cid id) (set! cepoch epoch) (set! cvalue x)
          x)))))

(defn late [^ISite site q] (.lookup site q))

(defn- deopt-dyn
  "A nested machine started from compiled code handles no effects itself:
   every operation abandons the compiled call (L4.exec.deopt)."
  [dyn]
  (assoc dyn :defaults (into {} (map (fn [[op _]] [op (fn [_ _] (m/abandon! :effect))]))
                             (:defaults dyn))))

(defn- nested [f args]
  (let [^objects c (m/current-context)]
    (m/call-in [(aget c 0) (aget c 1) (deopt-dyn (aget c 2))] f args true)))

(defn call
  "Call any function value from compiled code (L4.lower.calls): compiled
   callees directly, Klara closures in a nested machine, host functions as
   they are."
  [f args]
  (cond
    (instance? klara.runtime.value.IExecutable f)
    (let [^objects c (m/current-context)
          r (v/-call f (aget c 0) (aget c 1) (aget c 2) args)]
      (if (identical? r v/fallback) (nested f args) r))
    (or (instance? Closure f) (instance? klara.runtime.value.Continuation f) (m/intrinsic? f))
    (nested f args)
    :else (apply f args)))

;; ---------------------------------------------------------------------------
;; Lowering

(def ^:private unsupported #{:try :interop :code :hole :def :letrec})

(defn- link-value [link]
  (case (:kind link)
    :pinned (klara.runtime.world/pin (:world link) (:name link))
    :guarded (:value link)
    nil))

(defn- lower* [t consts self-name self-sym]
  (letfn [(constant [x]
            (let [i (count @consts)] (swap! consts conj x) (list 'clojure.core/nth 'consts i)))
          (go [t]
            (case (:op t)
              :const (let [x (:value t)]
                       (if (or (nil? x) (number? x) (string? x) (keyword? x) (boolean? x) (char? x))
                         x (constant x)))
              :local (:name t)
              :host (let [q (:name t)]
                      (cond (and (= "clojure.core" (namespace q)) (not (m/intrinsic? (m/host-value q)))) q
                            (:symbol (klara.lang.builtins/lookup q)) (:symbol (klara.lang.builtins/lookup q))
                            :else (constant (m/host-value q))))
              :global (let [l (:link t)]
                        (cond
                          ;; a recursive call of the definition being compiled: its own
                          ;; generation is a premise, so it denotes this function (L4.exec.valid)
                          (and (= :late (:kind l)) self-name (= (:name l) self-name)) self-sym
                          (= :late (:kind l))
                          (list 'klara.compile.lower/late (constant (Site. nil -1 nil)) (list 'quote (:name l)))
                          :else (constant (link-value l))))
              :fn (let [self (or (:self t) (t/fresh "fn"))]
                    (list* 'fn* self
                           (for [{:keys [params rest body]} (:arities t)]
                             (list (cond-> (vec params) rest (conj '& rest))
                                   (list 'klara.compile.lower/tick!)
                                   (go body)))))
              :app (let [f (:fn t) args (map go (:args t))]
                     (cond
                       (:recur t) (list* 'recur args)
                       (and (= :host (:op f)) (= "clojure.core" (namespace (:name f)))
                            (not (m/intrinsic? (m/host-value (:name f)))))
                       (list* (:name f) args)
                       (and (= :host (:op f)) (:symbol (klara.lang.builtins/lookup (:name f))))
                       (list* (:symbol (klara.lang.builtins/lookup (:name f))) args)
                       (and self-name (= :global (:op f)) (= :late (get-in f [:link :kind])) (= self-name (get-in f [:link :name])))
                       (list* self-sym args)
                       :else (list 'klara.compile.lower/call (go f) (vec args))))
              :recur (list* 'recur (map go (:args t)))
              :let (list 'let* [(:name t) (go (:init t))] (go (:body t)))
              :if (list 'if (go (:test t)) (go (:then t)) (go (:else t)))
              :do (list* 'do (map go (:body t)))
              :throw (list 'throw (go (:ex t)))
              (fail :L4.lower.subset (str "the backend does not compile " (:op t)))))]
    (go t)))

(defn subset-violation
  "The first construct outside the compilable subset (L4.lower.subset), or nil."
  [term]
  (some (fn [n]
          (cond (contains? unsupported (:op n)) (:op n)
                (and (= :host (:op n)) (m/intrinsic? (m/host-value (:name n)))) (:name n)))
        (t/nodes term)))

(defn lower
  "Compile a :fn term to a host function. With :self-name, late references
   to that definition call the compiled function itself."
  ([term] (lower term {}))
  ([term {:keys [self-name]}]
  (when-not (= :fn (:op term)) (fail :L4.lower.subset "only functions are compiled"))
  (when-let [x (subset-violation term)]
    (fail :L4.lower.subset (str "the backend does not compile " x)))
  (let [consts (atom [])
        self-sym (or (:self term) (t/fresh "self"))
        term (assoc term :self self-sym)
        form (lower* term consts self-name self-sym)
        wrapper (list 'fn* ['consts] form)]
    {:form form
     :fn ((binding [*ns* (the-ns 'klara.compile.lower)] (eval wrapper)) @consts)})))
