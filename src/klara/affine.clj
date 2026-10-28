(ns klara.affine
  "A conservative first affine fragment over K0. Derivations are EDN;
  rejection is mandatory only in declared mode. No host purity claims."
  (:require [klara.core :as c]))

(def version "s10-1")
(def pure-functions
  (into {} (for [s (keys c/prims)] [(symbol "clojure.core" (name s)) s])))

(def ^:private scalar-classes
  (set (map class [true 1 (int 1) (short 1) (byte 1) 1.0 (float 1.0)
                   1N 1M 1/2 (biginteger 1) "" \a :k 's])))
(def ^:private collection-classes
  (set (map class [[] {} #{} (list 1) '() (vec (range 40)) (into {} (map #(vector % %) (range 40)))])))

(defn value?
  "Closed immutable host data admitted by the erased boundary. Exact
  classes exclude user implementations of collection/number protocols;
  lazy sequences and arbitrary host objects fall back before effects."
  [v]
  (or (nil? v) (contains? scalar-classes (class v))
      (and (contains? collection-classes (class v))
           (if (map? v) (every? (fn [[k x]] (and (value? k) (value? x))) v)
             (every? value? v)))))

(defn check
  "Return an EDN derivation or nil (:inferred, default). :declared throws
  diagnostics with a source path. Parameters are copyable inputs; owned
  boundary contracts and unknown calls stay dynamic, outside this fragment."
  ([term] (check term :inferred))
  ([term mode]
   (try
     (c/assert-wf! term)
     (let [state (atom {}) rules (atom [])
           fail (fn [path message] (throw (ex-info (str "affine: " message)
                                                    {:klara/error :affine :path path :diagnostic message})))
           value {:kind :value}]
       (letfn [(owned? [v] (= :owned (:kind v)))
               (copyable! [v p]
                 (when-not (= :value (:kind v)) (fail p "owned value or function escapes its place")))
               (live! [v p]
                 (when-not (and (owned? v) (= :live (get-in @state [(:id v) :status])))
                   (fail p "double use, use after move, or unavailable owned place")))
               (full! [v p]
                 (live! v p)
                 (when-not (= :write (:permission v)) (fail p "write through a borrow")))
               (note! [t p v]
                 (swap! rules conj (cond-> {:path p :rule (if (= :perform (:op t)) (:name t) (:op t))}
                                    (owned? v) (assoc :resource (:id v)))) v)
               (walk [t env p pure?]
                 (let [go #(walk %1 env (conj p %2) pure?)
                       result
                       (case (:op t)
                         :quote (do
                                  ;; Host objects (including authority tokens) are not static constants.
                                  (when-not (value? (:datum t))
                                    (fail p "opaque constant")) value)
                         :local (let [v (nth env (- (count env) 1 (:index t)))]
                                  (when (owned? v) (live! v p)) v)
                         :prim (do (doseq [[i a] (map-indexed vector (:args t))]
                                     (copyable! (walk a env (conj p :args i) pure?) p)) value)
                         :let (let [v (go (:init t) :init)]
                                (walk (:body t) (conj env v) (conj p :body) pure?))
                         :if (do (copyable! (go (:test t) :test) p)
                                 (let [before @state a (go (:then t) :then) after @state
                                       _ (reset! state before) b (go (:else t) :else)]
                                   (when-not (and (= after @state) (= a b))
                                     (fail p "branches disagree on ownership")) a))
                         :fn (let [before @state]
                               (copyable! (walk (:body t) (into env (repeat (:arity t) value))
                                                (conj p :body) true) p)
                               (when (or (:rest? t) (not= before @state)) (fail p "impure callback"))
                               {:kind :function})
                         :app (let [f (go (:fn t) :fn)]
                                (when pure? (fail p "recursive call in a pure callback"))
                                (when-not (= :loop (:kind f)) (fail p "unknown call"))
                                (when-not (= (:arity f) (count (:args t))) (fail p "loop arity"))
                                (doseq [[i a] (map-indexed vector (:args t))]
                                  (copyable! (walk a env (conj p :args i) pure?) p))
                                (when-not (= (:state f) @state) (fail p "loop back edge changes ownership"))
                                value)
                         :letrec (let [f (first (:inits t)) before @state
                                       loop-f {:kind :loop :arity (:arity f) :state before}
                                       e (conj env loop-f)]
                                   (when (or pure? (not= 1 (count (:inits t))) (:rest? f))
                                     (fail p "unsupported recursion"))
                                   (copyable! (walk (:body f) (into e (repeat (:arity f) value))
                                                    (conj p :inits 0 :body) false) p)
                                   (when-not (= before @state) (fail p "loop changes ownership"))
                                   (walk (:body t) e (conj p :body) false))
                         :perform
                         (let [op (:name t) args (:args t)
                               arg (fn [i] (walk (nth args i) env (conj p :args i) pure?))]
                           (when (:target t) (fail p "user effect"))
                           (when (and pure? (not= op :host/var)) (fail p "effect in a pure callback"))
                           (case op
                             :host/var (if (and (= 1 (count args)) (= :quote (:op (first args)))
                                               (pure-functions (:datum (first args))))
                                         {:kind :function} (fail p "unknown host function"))
                             :own/alloc (do (when-not (= 1 (count args)) (fail p "alloc arity"))
                                            (copyable! (arg 0) p)
                                            (swap! state assoc p {:status :live :permission :write})
                                            {:kind :owned :id p :permission :write})
                             :own/borrow
                             (let [v (arg 0) f (second args) id (conj p :loan)]
                               (live! v p)
                               (when-not (and (= 2 (count args)) (= :fn (:op f))
                                              (= 1 (:arity f)) (not (:rest? f)))
                                 (fail p "borrow requires a lexical body"))
                               (swap! state assoc-in [(:id v) :status] :lent)
                               (swap! state assoc id {:status :live :permission :read})
                               (let [r (walk (:body f) (conj env {:kind :owned :id id :permission :read})
                                             (conj p :args 1 :body) false)]
                                 (copyable! r p)
                                 (swap! state dissoc id)
                                 (swap! state assoc-in [(:id v) :status] :live)
                                 r))
                             (:own/read :own/update :own/move :own/freeze :own/drop)
                             (let [v (arg 0)]
                               (live! v p)
                               (when-not (= op :own/read) (full! v p))
                               (when-not (if (= op :own/update) (<= 2 (count args)) (= 1 (count args)))
                                 (fail p "owned operation arity"))
                               (swap! rules conj {:path p :rule :permission :resource (:id v)
                                                  :operation op :permission (:permission v)})
                               (case op
                                 :own/read value
                                 :own/update (do (when-not (= :function (:kind (arg 1)))
                                                   (fail p "update requires a pure callback"))
                                                 (doseq [i (range 2 (count args))] (copyable! (arg i) p)) v)
                                 :own/move (do (swap! state assoc-in [(:id v) :status] :dead)
                                               (swap! state assoc p {:status :live :permission :write})
                                               {:kind :owned :id p :permission :write})
                                 (:own/freeze :own/drop) (do (swap! state assoc-in [(:id v) :status] :dead) value)))
                             (fail p "operation outside the static fragment")))
                         (fail p "form outside the static fragment"))]
                   (note! t p result)))]
         (let [function? (= :fn (:op term))
               _ (when (and function? (:rest? term)) (fail [] "variadic region"))
               result (if function?
                        (walk (:body term) (vec (repeat (:arity term) value)) [:body] false)
                        (walk term [] [] false))]
           (copyable! result [])
           (when (some #(= :live (:status %)) (vals @state))
             (fail [] "owned place must be frozen or dropped before region exit"))
           {:checker version :inputs :closed-immutable-data :code-id (c/code-id term) :rules @rules :exit @state})))
     (catch clojure.lang.ExceptionInfo e
       (when (= mode :declared) (throw e))))))

(defn verify! [term derivation]
  (when-not (= derivation (check term :declared))
    (throw (ex-info "affine: derivation does not match this term" {:klara/error :affine})))
  derivation)
