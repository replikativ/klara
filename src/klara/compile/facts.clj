(ns klara.compile.facts
  "Facts about definitions (design/06-speculation.md#3-facts), computed by
  the kernel's own analyses. The first is purity (L4.facts.pure): calling the
  definition on data cannot mutate anything that existed before the call or
  perform an effect, so running it to measure it (the investor) changes
  nothing but time. Conservative: what the analysis cannot see through is
  not pure."
  (:require [klara.lang.builtins :as b]
            [klara.lang.term :as t]
            [klara.runtime.value :as v]
            [klara.runtime.world :as w]))

(def ^:private allocating
  "Host functions that return a fresh object (mutable or not)."
  '#{clojure.core/boolean-array clojure.core/byte-array clojure.core/char-array
     clojure.core/short-array clojure.core/int-array clojure.core/long-array
     clojure.core/float-array clojure.core/double-array clojure.core/object-array
     clojure.core/make-array clojure.core/ex-info clojure.core/with-meta clojure.core/meta})

(def ^:private array-writes
  '#{clojure.core/aset clojure.core/aset-int clojure.core/aset-long clojure.core/aset-double
     clojure.core/aset-boolean clojure.core/aset-byte clojure.core/aset-char clojure.core/aset-short
     clojure.core/aset-float})

(def ^:private reads
  "Host functions that read objects without changing them."
  '#{clojure.core/aget clojure.core/alength})

(defn- pure-host? [q]
  (or (and (= "clojure.core" (namespace q)) (contains? b/pure-host (symbol (name q))))
      (contains? allocating q)
      (contains? reads q)
      (:pure (b/lookup q))
      ;; Klara's owned operations act persistently outside owned compiled code
      (contains? '#{klara.core/conj! klara.core/assoc! klara.core/dissoc! klara.core/disj!
                    klara.core/pop! klara.core/persistent! klara.core/transient klara.core/own} q)))

;; ---------------------------------------------------------------------------
;; Effect classes (L4.facts.effect), ordered by what can contain them

(def classes
  "From the least effect to the most: pure (nothing needed), fresh (writes to
   objects allocated in the call: the call contains them), world (def, world
   updates: a job contains them), handled (perform, printing: a handler or a
   job), shared (writes to objects that existed before: nothing), outside
   (host interop, unknown host functions: nothing, not repeatable)."
  [:pure :fresh :world :handled :shared :outside])

(def ^:private rank (zipmap classes (range)))

(defn- join [a b] (if (>= (rank (:class a)) (rank (:class b))) a b))

(def ^:private none {:class :pure})

(defn- effect-of [c why] {:class c :why why})

(def ^:private intrinsic-classes
  "Klara intrinsics by effect class; one not listed is outside."
  (merge (zipmap '[klara.world/define klara.world/publish! klara.world/advance
                   klara.world/current klara.world/in klara.world/get klara.world/link klara.world/names
                   klara.world/id klara.world/generation klara.world/footprint]
                 (repeat :world))
         (zipmap '[klara.effect/perform klara.effect/handle* klara.core/print klara.core/println
                   klara.core/pr klara.core/prn klara.core/newline klara.core/printf]
                 (repeat :handled))
         (zipmap (map #(symbol "klara.core" (name %)) b/mutating-host) (repeat :shared))
         (zipmap '[klara.core/atom klara.core/volatile!] (repeat :fresh))
         (zipmap '[klara.stage/lift klara.stage/liftable? klara.stage/code? klara.stage/form
                   klara.code/free klara.code/children klara.code/with-children klara.code/view
                   klara.code/make klara.code/subst klara.code/unfold klara.code/known
                   klara.code/pure-host? klara.code/fn* klara.code/loop*]
                 (repeat :pure))))

(def ^:private calling-host
  "Host functions that call functions they are given (and do nothing else),
   with the argument positions they call (:all for every argument): their
   effect is their callbacks', which is analysed where a callback is written
   (an fn, a global) or is relative to a parameter."
  (merge (zipmap '[clojure.core/mapv clojure.core/map clojure.core/filter clojure.core/filterv
                   clojure.core/remove clojure.core/keep clojure.core/keep-indexed clojure.core/map-indexed
                   clojure.core/mapcat clojure.core/reduce clojure.core/reduce-kv clojure.core/apply
                   clojure.core/some clojure.core/every? clojure.core/not-any? clojure.core/not-every?
                   clojure.core/sort-by clojure.core/group-by clojure.core/partition-by
                   clojure.core/take-while clojure.core/drop-while clojure.core/iterate clojure.core/run!]
                 (repeat #{0}))
         {'clojure.core/update #{2} 'clojure.core/update-in #{2}}
         (zipmap '[clojure.core/comp clojure.core/partial clojure.core/juxt clojure.core/complement
                   clojure.core/fnil]
                 (repeat :all))))

(declare definition-effect)

(defn- host-effect [q t fresh]
  (cond (or (pure-host? q) (contains? calling-host q)) none
        (contains? array-writes q)
        (if (and (= :local (get-in t [:args 0 :op])) (contains? fresh (get-in t [:args 0 :name])))
          (effect-of :fresh (str "writes an array it allocated (" q ")"))
          (effect-of :shared (str "writes an array it did not allocate (" q ")")))
        (contains? intrinsic-classes q) (let [c (intrinsic-classes q)]
                                          (if (= :pure c) none (effect-of c (str "calls " q))))
        :else (effect-of :outside (str "calls " q))))

(defn- term-effect
  "The effect class of evaluating term t, with a reason. `fresh` holds locals
   bound to objects allocated in this call. Calls of the definition's own
   parameters are recorded as relative (L4.facts.effect)."
  [ctx t fresh]
  (let [go #(term-effect ctx % fresh)
        all (fn [ts] (reduce join none (map go ts)))
        param #(when (= :local (:op %)) (get (:params ctx) (:name %)))]
    (case (:op t)
      (:const :local :host) none
      :global (let [q (get-in t [:link :name])
                    d (w/lookup (:world ctx) q)
                    x (:value d)]
                (cond
                  (v/closure? x) (definition-effect ctx q)
                  ;; anything else callable (a host function, an intrinsic) is pure
                  ;; only if declared so; data is looked up when called
                  (and (instance? clojure.lang.IFn x) (not (v/data? x)) (not (v/declared-pure? x)))
                  (effect-of :outside (str "calls the host function in " q))
                  :else (do (when d (vswap! (:premises ctx) conj [q (:generation d)])) none)))
      ;; an inner function (a loop) may write arrays this call allocated: they
      ;; did not exist before the call either
      :fn (reduce join none (map (fn [a] (term-effect ctx (:body a) fresh)) (:arities t)))
      :let (join (go (:init t))
                 (term-effect ctx (:body t)
                              (cond-> fresh
                                (and (= :app (:op (:init t))) (= :host (get-in t [:init :fn :op]))
                                     (or (contains? allocating (get-in t [:init :fn :name]))
                                         (= :fresh (intrinsic-classes (get-in t [:init :fn :name])))))
                                (conj (:name t)))))
      :app (let [f (:fn t)]
             ;; a parameter called, or handed to a host function that calls it
             (when-let [i (param f)] (vswap! (:relative ctx) conj i))
             (when-let [called (and (= :host (:op f)) (calling-host (:name f)))]
               (doseq [[k a] (map-indexed vector (:args t))
                       :when (or (= :all called) (contains? called k))]
                 (when-let [i (param a)] (vswap! (:relative ctx) conj i))))
             (join (if (= :host (:op f)) (host-effect (:name f) t fresh) (go f))
                   (all (:args t))))
      :def (join (effect-of :world (str "defines " (:name t))) (go (:init t)))
      ;; templates build code: their holes run now, the template later
      :code (all (:holes t))
      (:if :do :recur :throw :try :letrec) (all (t/children t))
      (effect-of :outside (str "contains " (name (:op t)))))))

(defn- definition-effect
  "The effect of definition q's body; recursive definitions are assumed
   pure while being analysed."
  [ctx q]
  (if (contains? @(:seen ctx) q)
    none
    (do (vswap! (:seen ctx) conj q)
        (let [d (w/lookup (:world ctx) q)
              e (term-effect ctx (.-term ^klara.runtime.value.Closure (:value d)) #{})]
          (vswap! (:premises ctx) conj [q (:generation d)])
          (cond-> e (:why e) (update :why #(str (t/base-name q) " " %)))))))

(defn effect
  "L4.facts.effect: {:class c :premises #{[q g] ..} :relative #{i ..}} for the
   function definition q in `world`, with :why when c is not :pure. :relative
   are the parameters whose functions it calls (or hands to host functions):
   its effect is also theirs."
  [world q]
  (let [d (w/lookup world q)]
    (if-not (and d (v/closure? (:value d)))
      {:class :outside :why (str q " is not a function definition") :premises #{} :relative #{}}
      (let [term (.-term ^klara.runtime.value.Closure (:value d))
            params (when (= :fn (:op term))
                     (into {} (mapcat (fn [a] (map-indexed (fn [i p] [p i]) (:params a))) (:arities term))))
            ctx {:world world :seen (volatile! #{}) :premises (volatile! #{}) :relative (volatile! #{})
                 :params (or params {})}
            e (definition-effect ctx q)]
        (assoc e :premises @(:premises ctx) :relative @(:relative ctx))))))

(defn pure
  "L4.facts.pure: {:pure true :premises #{[q g] ..}} if calling the function
   definition q on data has effect class pure or fresh (L4.facts.effect),
   else {:pure false :why reason}."
  [world q]
  (let [e (effect world q)]
    (if (#{:pure :fresh} (:class e))
      {:pure true :premises (:premises e)}
      {:pure false :why (:why e)})))
