(ns klara.compile.lower
  "The backend (spec/L4-compiler.md#lowering): checked Core terms to JVM
  classes through the Clojure compiler.

  A lowered function is a host fn. Late links are looked up in the
  effective world of the call (L4.lower.links) through the runtime context
  `*ctx*`, the machine state of the call. Calls to Klara closures run in a
  nested machine whose effects abandon the compiled call (L4.lower.calls,
  L4.exec.deopt). Each lowering is compiled by `eval`, which uses a fresh
  class loader (L4.retain.classes)."
  (:require [klara.lang.term :as t]
            [klara.runtime.machine :as m]
            [klara.runtime.value :as v])
  (:import [klara.runtime.value Closure]))

(def ^:dynamic *ctx* "The machine state of the call that entered compiled code." nil)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

;; ---------------------------------------------------------------------------
;; Runtime support called from lowered code

(defn tick!
  "L4.lower.steps: one step per function entry and loop iteration."
  []
  (when-let [^longs meter (get-in *ctx* [:dyn :meter])]
    (aset meter 0 (dec (aget meter 0)))
    (when (neg? (aget meter 0)) (m/abandon! :exhausted))))

(defn late [q] (m/resolve-link {:kind :late :name q} (:world *ctx*)))

(defn- deopt-dyn
  "A nested machine started from compiled code handles no effects itself:
   every operation abandons the compiled call (L4.exec.deopt)."
  [dyn]
  (assoc dyn :defaults (into {} (map (fn [[op _]] [op (fn [_ _] (m/abandon! :effect))]))
                             (:defaults dyn))))

(defn call
  "Call any function value from compiled code (L4.lower.calls)."
  [f args]
  (if (or (instance? Closure f) (instance? klara.runtime.value.Continuation f) (m/intrinsic? f))
    (m/call-in (update *ctx* :dyn deopt-dyn) f args)
    (apply f args)))

;; ---------------------------------------------------------------------------
;; Lowering

(def ^:private unsupported #{:try :interop :code :hole :def :letrec})

(defn- link-value [link]
  (case (:kind link)
    :pinned (klara.runtime.world/pin (:world link) (:name link))
    :guarded (:value link)
    nil))

(defn- lower* [t consts]
  (letfn [(constant [x]
            (let [i (count @consts)] (swap! consts conj x) (list 'clojure.core/nth 'consts i)))
          (go [t]
            (case (:op t)
              :const (let [x (:value t)]
                       (if (or (nil? x) (number? x) (string? x) (keyword? x) (boolean? x) (char? x))
                         x (constant x)))
              :local (:name t)
              :host (let [q (:name t)]
                      (if (and (= "clojure.core" (namespace q)) (not (m/intrinsic? (m/host-value q))))
                        q (constant (m/host-value q))))
              :global (let [l (:link t)]
                        (if (= :late (:kind l))
                          (list 'klara.compile.lower/late (list 'quote (:name l)))
                          (constant (link-value l))))
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
  "Compile a :fn term to a host function."
  [term]
  (when-not (= :fn (:op term)) (fail :L4.lower.subset "only functions are compiled"))
  (when-let [x (subset-violation term)]
    (fail :L4.lower.subset (str "the backend does not compile " x)))
  (let [consts (atom [])
        form (lower* term consts)
        wrapper (list 'fn* ['consts] form)]
    {:form form
     :fn ((binding [*ns* (the-ns 'klara.compile.lower)] (eval wrapper)) @consts)}))
