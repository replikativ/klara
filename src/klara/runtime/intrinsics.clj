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
      ;; L2.view.total: every construct has a view
      :fn (let [[a & more] (:arities t)
                arities (mapv (fn [a] {:params (:params a) :rest (:rest a) :body (c (:body a))}) (:arities t))]
            (cond-> {:op :fn :self (:self t) :arities arities}
              ;; the common case keeps its flat shape
              (and (nil? more) (nil? (:rest a))) (assoc :params (:params a) :body (c (:body a)))))
      :letrec {:op :letrec :bindings (mapv (fn [[n f]] [n (c f)]) (:bindings t)) :body (c (:body t))}
      :throw {:op :throw :ex (c (:ex t))}
      :try {:op :try :body (c (:body t))
            :catches (mapv (fn [k] {:class (:class k) :name (:name k) :body (c (:body k))}) (:catches t))
            :finally (some-> (:finally t) c) :code code}
      :interop (cond-> {:op :interop :static? (boolean (:static? t)) :new? (boolean (:new? t))
                        :member (:member t) :args (mapv c (:args t)) :code code}
                 (:static? t) (assoc :target (:target t))
                 (not (:static? t)) (assoc :target (c (:target t))))
      :def {:op :def :name (:name t) :init (c (:init t)) :code code}
      :code {:op :code :template (c (:template t)) :holes (mapv c (:holes t)) :code code}
      :hole {:op :hole :index (:index t) :code code}))

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
      :fn (t/fn-term (:self m)
                     (if (:arities m)
                       (if (and (:body m) (= 1 (count (:arities m))))
                         [(t/arity (:params m) nil (term-of (:body m)))]   ; the flat shape wins if edited
                         (mapv (fn [a] (t/arity (:params a) (:rest a) (term-of (:body a)))) (:arities m)))
                       [(t/arity (:params m) nil (term-of (:body m)))]))
      :letrec {:op :letrec :bindings (mapv (fn [[n f]] [n (term-of f)]) (:bindings m)) :body (term-of (:body m))}
      :throw {:op :throw :ex (term-of (:ex m))}
      ;; constructs with fields that are not children are rebuilt from the
      ;; original they came from (:code of the view), with new children
      :try (t/with-children (term-of (:code m))
             (cond-> (into [(term-of (:body m))] (map (comp term-of :body) (:catches m)))
               (:finally m) (conj (term-of (:finally m)))))
      :interop (t/with-children (term-of (:code m))
                 (cond->> (mapv term-of (:args m))
                   (not (:static? m)) (cons (term-of (:target m)))))
      :def (t/with-children (term-of (:code m)) [(term-of (:init m))])
      :code (t/with-children (term-of (:code m)) (into [(term-of (:template m))] (map term-of (:holes m))))
      :hole (term-of (:code m))
      (fail :L2.view.make (str "cannot make code from view " (:op m))))))

(defintrinsic klara.code/view [st [code]] (ret st (view code)))

(defintrinsic klara.code/make [st [m]] (ret st (Code. (t/refresh-free (make m nil)))))

(defintrinsic klara.code/subst [st [code bindings]]
  (ret st (Code. (t/refresh-free (t/substitute (term-of code) (into {} (map (fn [[n x]] [n (term-of x)])) bindings))))))

(defintrinsic klara.code/unfold [st [code]]                    ; L2.view.unfold
  ;; The function a global link or lifted closure denotes, as code with fresh
  ;; binders, or nil: for a global, its definition (the reference, also when
  ;; compiled code is installed for it). Untrusted: recipes use it, the
  ;; checker re-derives what it needs.
  (let [t (term-of code)
        f (case (:op t)
            :global (let [{:keys [kind name world]} (:link t)
                          x (if (= :pinned kind) (w/pin world name) (:value (w/lookup (:world st) name)))]
                      (when (v/closure? x) x))
            :const (when (v/closure? (:value t)) (:value t))
            nil)]
    (ret st (when f (Code. (first (t/freshen (.-term ^Code (reify-closure f)))))))))

(defintrinsic klara.code/known [st [code]]                     ; L2.view.known
  ;; Code for the value of a constant or of a global defined as immutable data
  ;; (L4.check.delta-data), or nil.
  (let [t (term-of code)
        x (case (:op t)
            :const [(:value t)]
            :global (let [{:keys [kind name world]} (:link t)
                          d (when-not (= :pinned kind) (w/lookup (:world st) name))
                          v (if (= :pinned kind) (w/pin world name) (:value d))]
                      (when (and (not (:macro? d)) (not (v/closure? v)) (v/data? v)) [v]))
            nil)]
    (ret st (when x (Code. (t/const (first x)))))))

(defintrinsic klara.code/pure-host? [st [code]]                ; L2.view.known
  ;; Is code a host function the checker may evaluate on constants (L4.check.prim)?
  (let [t (term-of code)
        q (:name t)]
    (ret st (boolean (and (= :host (:op t))
                          (or (and (= "clojure.core" (namespace q)) (contains? b/pure-host (symbol (name q))))
                              (:pure (b/lookup q))))))))

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
