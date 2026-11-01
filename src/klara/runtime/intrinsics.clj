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
   lifted, globals linked according to the closure's basis."
  [^Closure f]
  (let [term (.-term f)
        env (v/captured f)
        rec (fn [x] (if (instance? clojure.lang.IDeref x) (if (v/closure? @x) @x x) x))
        body (t/substitute term (into {} (map (fn [[n x]] [n (m/lift-term (rec x))])) env))
        body (if-let [b (.-basis f)] (pin-links body b) body)]
    (Code. (t/refresh-free body))))

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

(defn view [^Code code]
  (let [t (.-term code)]
    (case (:op t)
      :const {:op :const :value (:value t)}
      :local {:op :local :name (:name t)}
      :host {:op :host :name (:name t)}
      :global {:op :global :name (get-in t [:link :name]) :kind (get-in t [:link :kind])}
      :app {:op :app :fn (c (:fn t)) :args (mapv c (:args t))}
      :let {:op :let :name (:name t) :init (c (:init t)) :body (c (:body t))}
      :if {:op :if :test (c (:test t)) :then (c (:then t)) :else (c (:else t))}
      :do {:op :do :body (mapv c (:body t))}
      :fn (let [[a & more] (:arities t)]
            (if (and (nil? more) (nil? (:rest a)))
              {:op :fn :self (:self t) :params (:params a) :body (c (:body a))}
              {:op :other}))
      {:op :other})))

(defn make [code-or-view original]
  (let [m code-or-view]
    (case (:op m)
      :const (t/const (:value m))
      :local (t/local (:name m))
      :app (t/app (term-of (:fn m)) (map term-of (:args m)))
      :let (t/let1 (:name m) (term-of (:init m)) (term-of (:body m)))
      :if (t/if* (term-of (:test m)) (term-of (:then m)) (term-of (:else m)))
      :do (t/do* (mapv term-of (:body m)))
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

(defintrinsic klara.profile/snapshot [st [f]]                   ; L4.profile.snapshot
  (ret st (cond
            (v/closure? f) (profile-snapshot f)
            (instance? klara.runtime.value.IExecutable f)
            (let [r (:reference (v/-describe f))]
              {:compiled true :reference r})
            :else (fail :L4.profile.snapshot (str "no profile for " (pr-str f))))))

(defintrinsic klara.profile/reset! [st [on?]]
  (reset! prep/profiling (boolean on?))
  (ret st on?))
