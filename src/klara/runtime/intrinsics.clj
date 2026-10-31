(ns klara.runtime.intrinsics
  "Runtime-provided guest functions: klara.world, klara.stage, klara.effect
  and the klara.core functions whose meaning involves effects.

  Each intrinsic receives the machine state and its arguments and returns a
  new state. Rule IDs refer to spec/."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.machine :as m]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w])
  (:import [klara.runtime.value Closure Code World]))

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
    (assoc st :mode :eval :ctl term :env {})))

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
        env (.-env f)
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
