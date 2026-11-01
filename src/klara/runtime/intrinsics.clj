(ns klara.runtime.intrinsics
  "Runtime-provided guest functions: klara.world, klara.stage, klara.effect
  and the klara.core functions whose meaning involves effects.

  Each intrinsic receives the machine state and its arguments and returns a
  new state. Rule IDs refer to spec/."
  (:require [klara.lang.builtins :as b]
            [klara.runtime.prims :as prims]
            [klara.runtime.prepare :as prep]
            [klara.lang.term :as t]
            [klara.runtime.machine :as m]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Closure Code World]))

(set! *warn-on-reflection* true)

(defn fail [rule msg & {:as data}]
  (throw (ex-info msg (merge {:rule rule :message msg} data))))

(defn- ret [st x] (assoc st :mode :ret :ctl x :env nil))

(defmacro defintrinsic
  "Register guest function `q` whose body sees the machine state `st` and
   the argument vector `args`."
  [q [st args] & body]
  `(b/register! '~q {:kind :intrinsic :fn (fn [~st ~args] ~@body)}))

(defn- check-world [x]
  (when-not (v/world? x) (fail :L1.world.value (str "expected a world, got " (pr-str x))))
  x)

;; ---------------------------------------------------------------------------
;; klara.world (L1.context.*)

(defintrinsic klara.world/current [st _] (ret st (:world st)))  ; L1.context.current

(defintrinsic klara.world/in [st [world f & args]]              ; L1.context.in
  (check-world world)
  (assoc st :mode :apply :ctl [f (vec args)]
         :k (conj (:k st) {:f :restore :world (:world st) :mint (:mint st)})
         :world world :mint world))

(defintrinsic klara.world/get [st [world q]]                    ; L1.context.get
  (ret st (w/pin (check-world world) q)))

(defintrinsic klara.world/define [st [world q value]]           ; L1.world.define
  (check-world world)
  (ret st (w/put-definition world q (w/definition q {:value value :term (t/const value)}))))

(defintrinsic klara.world/publish! [st [world]]                 ; L1.session.publish
  (check-world world)
  (m/perform st :world/update [(fn [_] world)]))

(defintrinsic klara.world/advance [st _]                        ; L1.context.advance
  (when (:mint st) (fail :L1.context.advance "world/advance in a pinned context"))
  (let [session (get-in st [:dyn :session])]
    (assoc (ret st nil) :world (if (get-in st [:dyn :job]) (:world st) (:world @session)))))

(defintrinsic klara.world/link [st [world q]]                   ; L2.link.pinned
  (check-world world)
  (ret st (Code. {:op :global :link {:kind :pinned :world (w/slice world (w/footprint world q)) :name q}})))

(defintrinsic klara.world/names [st [world ns-sym]]              ; L1.world.names
  (ret st (vec (sort (filter #(= (str ns-sym) (namespace %)) (keys (w/defs (check-world world))))))))

(defintrinsic klara.world/id [st [world]] (ret st (w/id (check-world world))))

(defintrinsic klara.world/generation [st [world q]] (ret st (w/generation (check-world world) q)))

(defintrinsic klara.world/footprint [st [x]]                    ; L1.slice.footprint
  (ret st (cond
            (and (v/closure? x) (.-basis ^Closure x)) (let [^World b (.-basis ^Closure x)] (.-footprint b))
            :else nil)))

;; ---------------------------------------------------------------------------
;; klara.stage (spec/L2-staging.md)

(b/register! 'klara.stage/code {:kind :special})
(b/register! 'klara.stage/esc {:kind :special})

(defintrinsic klara.stage/lift [st [x]] (ret st (Code. (m/lift-term x))))   ; L2.lift.values

(defintrinsic klara.stage/run [st [c]]                          ; L2.run.*
  (when-not (v/code? c) (fail :L2.run.closed (str "run expects code, got " (pr-str c))))
  (let [term (.-term ^Code c) free (t/free-locals term)]
    (when (seq free)
      (fail :L2.run.closed (str "code has free locals " (vec free)) :locals (vec free)))
    (assoc st :mode :eval :ctl (m/prepare-term term) :env [])))

(defn pin-links
  "Replace late links by links pinned to `world` (L2.reify.fn, L4.pin.links)."
  [term world]
  (if (= :global (:op term))
    (let [l (:link term)]
      (if (= :late (:kind l))
        {:op :global :link {:kind :pinned :world world :name (:name l)}}
        term))
    (t/with-children term (map #(pin-links % world) (t/children term)))))

(defn reify-closure
  "Code with the structure of closure `f` (L2.reify.fn): captured locals are
   lifted, globals linked according to the closure's basis. `term` may be
   the closure's term with annotations (see annotated-reference)."
  ([f] (reify-closure f (.-term ^Closure f)))
  ([^Closure f term]
  (let [env (v/captured f)
        rec (fn [x] (if (instance? clojure.lang.IDeref x) (if (v/closure? @x) @x x) x))
        body (t/substitute term (into {} (map (fn [[n x]] [n (m/lift-term (rec x))])) env))
        body (if-let [b (.-basis f)] (pin-links body b) body)]
    (Code. (t/refresh-free body)))))

(defintrinsic klara.stage/reify [st [f]]                        ; L2.reify.*
  (ret st (cond
            (v/closure? f) (reify-closure f)
            (v/code? f) (Code. (m/lift-term f))
            (fn? f) (Code. (m/lift-term f))                     ; L2.reify.host
            :else (fail :L2.reify.fn (str "cannot reify " (pr-str f))))))

(defintrinsic klara.stage/code? [st [x]] (ret st (v/code? x)))

(defintrinsic klara.stage/form [st [c]] (ret st (v/code-form c)))

;; ---------------------------------------------------------------------------
;; klara.effect (spec/L3-effects.md)

(defintrinsic klara.effect/perform [st [op & args]]             ; L3.perform.op
  (when-not (keyword? op) (fail :L3.perform.op (str "operation must be a keyword, got " (pr-str op))))
  (m/perform st op (vec args)))

(defintrinsic klara.effect/handle* [st [handlers thunk]]        ; L3.handle.deep
  (when-not (map? handlers) (fail :L3.handle.deep "handlers must be a map of operation to function"))
  (assoc st :mode :apply :ctl [thunk []]
         :k (conj (:k st) {:f :handle :handlers (dissoc handlers :return) :return (:return handlers)
                           :world (:world st) :mint (:mint st)})))

(b/register! 'klara.effect/handle
             {:kind :macro
              :fn (fn [[_ handlers & body] _env]
                    (list 'klara.effect/handle* handlers (list* 'fn* [] body)))})

;; ---------------------------------------------------------------------------
;; klara.core: printing performs :io/print; host mutation is checked in jobs

(doseq [[s f] {'print print 'println println 'pr pr 'prn prn 'newline newline 'printf printf}]
  (b/register! (symbol "klara.core" (name s))
               {:kind :intrinsic
                :fn (fn [st args]
                      (let [text (with-out-str (apply f args))]
                        (m/perform st :io/print [text])))}))

(defn- owned? [st x]
  (let [job (get-in st [:dyn :job])]
    (or (nil? job) (contains? (:owned @job) x))))

(doseq [s b/mutating-host]
  (let [hf @(resolve (symbol "clojure.core" (name s)))]
    (b/register! (symbol "klara.core" (name s))
                 {:kind :intrinsic
                  :fn (fn [st [target & more :as args]]
                        (when-not (owned? st target)
                          (fail :L3.job.host-mutation
                                (str (name s) " on an object created outside this job")
                                :hint "create the atom inside the job, or return a value instead"))
                        (assoc st :mode :apply :ctl [hf (vec args)]))})))

(doseq [[s f] {'atom atom 'volatile! volatile!}]
  (b/register! (symbol "klara.core" (name s))
               {:kind :intrinsic
                :fn (fn [st args]
                      (let [x (apply f args)]
                        (when-let [job (get-in st [:dyn :job])]
                          (swap! job update :owned (fnil conj #{}) x))
                        (ret st x)))}))

;; vswap! is a macro in Clojure: (vswap! v f & args) = (vreset! v (f @v args..))
(b/register! 'klara.core/vswap!
             {:kind :macro
              :fn (fn [[_ v f & args] _env]
                    (let [x (gensym "v")]
                      (list 'clojure.core/let [x v]
                            (list 'clojure.core/vreset! x (list* f (list 'clojure.core/deref x) args)))))})

;; defrecord (L0.surface.defrecord): a record is a map of its fields, tagged
;; with its type in metadata; ->Name and map->Name construct it.
(b/register! 'klara.core/defrecord
             {:kind :macro
              :fn (fn [[_ nm fields & impls] env]
                    (when (seq impls)
                      (fail :L0.surface.defrecord "protocol implementations in defrecord are not supported yet"))
                    (let [tag (symbol (str (:ns env)) (name nm))
                          ks (mapv (comp keyword name) fields)
                          m (gensym "m")]
                      (list 'do
                            (list 'def nm (list 'quote tag))
                            (list 'defn (symbol (str "->" nm)) (vec fields)
                                  (list 'clojure.core/with-meta (zipmap ks fields) {:klara/record (list 'quote tag)}))
                            (list 'defn (symbol (str "map->" nm)) [m]
                                  (list 'clojure.core/with-meta (list 'clojure.core/merge (zipmap ks (repeat nil)) m)
                                        {:klara/record (list 'quote tag)})))))})

;; ---------------------------------------------------------------------------
;; klara.code: Code views for guest recipes (L2.view.make)
;;
;; A view is the top of a term as a map whose subterms are Code values (which
;; may have free locals bound by the enclosing term). Views are how guest
;; programs inspect and rebuild code; they grant no authority.

(defn- c [term] (Code. term))
(defn- term-of [x] (if (v/code? x) (.-term ^Code x) (fail :L2.view.make (str "expected code, got " (pr-str x)))))

(declare view*)

(defn view
  "The view of `code`; a term annotated with its profile (L4.jit.context)
   shows it under :profile."
  [^Code code]
  (let [t (.-term code)]
    (cond-> (view* code t) (:profile t) (assoc :profile (:profile t)))))

(defn- view* [^Code code t]
    (case (:op t)
      :const {:op :const :value (:value t)}
      :local {:op :local :name (:name t)}
      :host {:op :host :name (:name t)}
      :global {:op :global :name (get-in t [:link :name]) :kind (get-in t [:link :kind])}
      :app {:op :app :fn (c (:fn t)) :args (mapv c (:args t))}
      :let {:op :let :name (:name t) :init (c (:init t)) :body (c (:body t))}
      :if {:op :if :test (c (:test t)) :then (c (:then t)) :else (c (:else t))}
      :do {:op :do :body (mapv c (:body t))}
      :recur {:op :recur :target (:target t) :arity (:arity t) :args (mapv c (:args t))}
      :fn (let [[a & more] (:arities t)]
            (if (and (nil? more) (nil? (:rest a)))
              {:op :fn :self (:self t) :params (:params a) :body (c (:body a))}
              {:op :other :code code}))
      {:op :other :code code}))

(defintrinsic klara.code/children [st [code]]                  ; L2.view.children
  (ret st (mapv c (t/children (term-of code)))))

(defintrinsic klara.code/with-children [st [code cs]]          ; L2.view.children
  (let [t (term-of code)]
    (when-not (= (count cs) (count (t/children t)))
      (fail :L2.view.children (str "expected " (count (t/children t)) " children, got " (count cs))))
    (ret st (Code. (t/refresh-free (t/with-children t (mapv term-of cs)))))))

(defn make [code-or-view original]
  (let [m code-or-view]
    (case (:op m)
      :const (t/const (:value m))
      :local (t/local (:name m))
      ;; exactly what the expander would accept (L0.surface.unsupported):
      ;; registered functions, and clojure.core functions that are not macros
      ;; and not refused
      :host (let [q (:name m)
                  v (when (= "clojure.core" (namespace q)) (resolve q))]
              (if (or (b/lookup q)
                      (and (var? v) (not (:macro (meta v)))
                           (not (contains? b/unsupported (symbol (name q))))))
                (t/host q)
                (fail :L2.view.make (str "not a host function Klara supports: " q))))
      :app (t/app (term-of (:fn m)) (map term-of (:args m)))
      :let (t/let1 (:name m) (term-of (:init m)) (term-of (:body m)))
      :if (t/if* (term-of (:test m)) (term-of (:then m)) (term-of (:else m)))
      :do (t/do* (mapv term-of (:body m)))
      :recur {:op :recur :target (:target m) :arity (:arity m) :args (mapv term-of (:args m))}
      :fn (t/fn-term (:self m) [(t/arity (:params m) nil (term-of (:body m)))])
      (fail :L2.view.make (str "cannot make code from view " (:op m))))))

(defintrinsic klara.code/view [st [code]] (ret st (view code)))

(defintrinsic klara.code/make [st [m]] (ret st (Code. (t/refresh-free (make m nil)))))

(defintrinsic klara.code/subst [st [code bindings]]
  (ret st (Code. (t/refresh-free (t/substitute (term-of code) (into {} (map (fn [[n x]] [n (term-of x)])) bindings))))))

(defintrinsic klara.code/unfold [st [code]]
  ;; The function a global link or lifted closure denotes, as code with fresh
  ;; binders, or nil. Untrusted: recipes use it, the checker re-derives it.
  (let [t (term-of code)
        f (case (:op t)
            :global (let [x (m/resolve-link (:link t) (:world st))] (when (v/closure? x) x))
            :const (when (v/closure? (:value t)) (:value t))
            nil)]
    (ret st (when f (Code. (first (t/freshen (.-term ^Code (reify-closure f)))))))))

(defintrinsic klara.code/host-fn [st [code]]
  (let [t (term-of code)] (ret st (when (= :host (:op t)) (m/host-value (:name t))))))

;; ---------------------------------------------------------------------------
;; Primitives that correct host behaviour (klara.runtime.prims)

(b/register! 'klara.core/- {:kind :host :fn prims/- :symbol 'klara.runtime.prims/- :pure true})
;; owned updates: in place on transients, persistent otherwise (L4.check.in-place)
(doseq [s '[conj! assoc! dissoc! disj! pop! persistent! transient own]]
  (b/register! (symbol "klara.core" (name s))
               {:kind :host :fn @(ns-resolve 'klara.runtime.prims s) :symbol (symbol "klara.runtime.prims" (name s))}))
(b/register! 'klara.jit/same? {:kind :host :fn prims/same? :symbol 'klara.runtime.prims/same? :pure true})

;; ---------------------------------------------------------------------------
;; klara.profile: the interpreter's feedback as data (L4.profile.snapshot)

(defn- node-children [n]
  (let [tg (prep/tag n)]
    (case tg
      4 (map #(.-body ^klara.runtime.prepare.Arity %) (.-arities ^klara.runtime.prepare.Fn n))
      5 (cons (.-f ^klara.runtime.prepare.App n) (.-args ^klara.runtime.prepare.App n))
      6 [(.-init ^klara.runtime.prepare.Let n) (.-body ^klara.runtime.prepare.Let n)]
      7 (concat (.-fns ^klara.runtime.prepare.Letrec n) [(.-body ^klara.runtime.prepare.Letrec n)])
      8 [(.-test ^klara.runtime.prepare.If n) (.-then ^klara.runtime.prepare.If n) (.-else ^klara.runtime.prepare.If n)]
      9 (concat (.-exprs ^klara.runtime.prepare.Do n) [(.-last ^klara.runtime.prepare.Do n)])
      10 (.-args ^klara.runtime.prepare.Recur n)
      11 [(.-ex ^klara.runtime.prepare.Throw n)]
      12 (cons (.-body ^klara.runtime.prepare.Try n) (keep :body (.-catches ^klara.runtime.prepare.Try n)))
      13 (.-args ^klara.runtime.prepare.Interop n)
      14 [(.-init ^klara.runtime.prepare.Def n)]
      15 (.-holes ^klara.runtime.prepare.Code n)
      [])))

(defn- describe-callee [x]
  (cond (v/closure? x) (or (some-> (:self (.-term ^Closure x)) str) :fn)
        (keyword? x) x
        :else (str x)))

(defn profile-snapshot
  "The profile of closure `f`: its entries (argument classes and stable
   values), its calls and its branches, with source positions."
  [^Closure f]
  (let [root (.-node f)
        nodes (tree-seq (comp seq node-children) node-children root)
        pos #(:pos (.sourceTerm ^klara.runtime.prepare.INode %))
        snap #(.snapshot ^klara.runtime.prepare.IProfile %)]
    {:entries (snap (.-profile ^klara.runtime.prepare.Fn root))
     :calls (vec (for [n nodes :when (== 5 (prep/tag n))
                       :let [p (snap (.-profile ^klara.runtime.prepare.App n))]
                       :when (pos? (:count p))]
                   {:pos (pos n) :count (:count p) :callee (describe-callee (:callee p))}))
     :branches (vec (for [n nodes :when (== 8 (prep/tag n))
                          :let [[t e] (:branches (snap (.-profile ^klara.runtime.prepare.If n)))]
                          :when (pos? (+ t e))]
                      {:pos (pos n) :then t :else e}))}))

(defn- keep-root-profile
  "reify rebuilds the function term itself; its profile goes back on it."
  [^Code code p]
  (if p (Code. (assoc (.-term code) :profile p)) code))

(defn annotated-reference
  "Code of closure `f` whose terms carry their profiles under :profile
   (L4.jit.context): a function its entries, a call its count and callee,
   an if its branch counts. Prepared nodes share their terms, so the
   profiles are found by identity."
  [^Closure f]
  (let [root (.-node f)
        by-term (java.util.IdentityHashMap.)
        snap #(.snapshot ^klara.runtime.prepare.IProfile %)]
    (doseq [n (tree-seq (comp seq node-children) node-children root)]
      (case (prep/tag n)
        4 (.put by-term (.sourceTerm ^klara.runtime.prepare.INode n) (snap (.-profile ^klara.runtime.prepare.Fn n)))
        5 (let [p (snap (.-profile ^klara.runtime.prepare.App n))]
            (.put by-term (.sourceTerm ^klara.runtime.prepare.INode n)
                  {:count (:count p) :callee (describe-callee (:callee p))}))
        8 (let [[a b] (:branches (snap (.-profile ^klara.runtime.prepare.If n)))]
            (.put by-term (.sourceTerm ^klara.runtime.prepare.INode n) {:then a :else b}))
        nil))
    (letfn [(annotate [term]
              (let [cs (t/children term)
                    t' (if (seq cs) (t/with-children term (mapv annotate cs)) term)]
                (if-let [p (.get by-term term)] (assoc t' :profile p) t')))]
      (keep-root-profile (reify-closure f (annotate (.-term f)))
                         (.get by-term (.-term f))))))

;; Saved profiles (L4.profile.saved): profiles as data keyed by the path of
;; child indices from the function's term, for a later run (AOT).

(defn- edn-data? [x]
  (cond (or (nil? x) (boolean? x) (number? x) (string? x) (keyword? x) (symbol? x) (char? x)) true
        (or (vector? x) (set? x) (seq? x)) (every? edn-data? x)
        (map? x) (and (not (record? x)) (every? edn-data? (mapcat identity x)))
        :else false))

(defn- small-data?
  "EDN data of at most 64 scalars: worth saving as a stable value."
  [x]
  (and (edn-data? x)
       (<= (count (filter (complement coll?) (tree-seq coll? seq x))) 64)))

(defn- export-profile [p]
  (cond-> (dissoc p :sample)
    (:classes p) (update :classes (fn [cs] (mapv #(if (class? %) (.getName ^Class %) %) cs)))
    (:stable p) (update :stable (fn [vs] (mapv #(if (and (vector? %) (small-data? (second %))) % :unstable) vs)))
    (contains? p :callee) (update :callee #(if (or (string? %) (keyword? %) (nil? %)) % (str %)))))

(defn- import-profile [p]
  (cond-> p
    (:classes p) (update :classes (fn [cs] (mapv #(if (string? %)
                                                     (try (Class/forName ^String %) (catch Throwable _ :polymorphic))
                                                     %) cs)))))

(defn saved-profile
  "The profile of closure `f` as EDN data: {:form-hash h :paths {path profile}}."
  [^Closure f form]
  (let [paths (transient {})]
    (letfn [(walk [term path]
              (when-let [p (:profile term)] (assoc! paths path (export-profile p)))
              (doseq [[i c] (map-indexed vector (t/children term))] (walk c (conj path i))))]
      (walk (.-term ^Code (annotated-reference f)) []))
    {:form-hash (hash form) :paths (persistent! paths)}))

(defn reference-with-profile
  "Code of closure `f` annotated with a saved profile instead of its own."
  [^Closure f saved]
  (let [paths (:paths saved)]
    (letfn [(annotate [term path]
              (let [cs (t/children term)
                    t' (if (seq cs)
                         (t/with-children term (vec (map-indexed (fn [i c] (annotate c (conj path i))) cs)))
                         term)]
                (if-let [p (get paths path)] (assoc t' :profile (import-profile p)) t')))]
      (keep-root-profile (reify-closure f (annotate (.-term f) []))
                         (some-> (get paths []) import-profile)))))

(defn strip-annotations
  "The term without profile annotations."
  [term]
  (let [cs (t/children term)]
    (cond-> (dissoc term :profile)
      (seq cs) (t/with-children (mapv strip-annotations cs)))))

(defintrinsic klara.profile/snapshot [st [f]]                   ; L4.profile.snapshot
  (ret st (cond
            (v/closure? f) (profile-snapshot f)
            (instance? klara.runtime.value.IExecutable f)
            (let [r (:reference (v/-describe f))]
              {:compiled true :reference r})
            :else (fail :L4.profile.snapshot (str "no profile for " (pr-str f))))))

(defintrinsic klara.profile/record! [st [on?]]                 ; L4.profile.record
  (reset! prep/profiling (boolean on?))
  (ret st on?))
