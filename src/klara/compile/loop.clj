(ns klara.compile.loop
  "Structural direct self-tail loops and ordered parallel transfers in named IR.
   No purity, layout, ownership, trip-count or recovery-reachability claim. Paths
   are relative to the supplied IR node, not invented original-Core locations."
  (:require [klara.core :as core]))

(defn- reject! [check path]
  (throw (ex-info "unsupported direct tail loop"
                  {:reason :unsupported-loop :check check :path path})))

(defn transfer
  "All RHSs evaluate in order before any destination is written. Temporary
   indices are plan-local, independent of backend variable names. Loop targets
   are distinct; repeated private-vector stores need their own update contract."
  [destinations arguments]
  (when-not (and (vector? destinations) (vector? arguments)
                 (= (count destinations) (count arguments))
                 (every? some? destinations)
                 (= (count destinations) (count (distinct destinations))))
    (reject! :transfer-interface []))
  {:evaluations (mapv (fn [i expression] {:temporary i :expression expression})
                      (range) arguments)
   :commits (mapv (fn [destination i] {:destination destination :temporary i})
                  destinations (range))})

(defn check-transfer!
  "Independently bind the canonical temporary/commit schedule to its source.
   Representation-sensitive CodeIDs prevent equal Long/BigInt literals from
   being exchanged. This structural adapter is tested hosted code, not itself
   a proof of expression evaluation, Java lowering or arbitrary host identity."
  [destinations arguments plan]
  (when-not (and (vector? destinations) (vector? arguments)
                 (= (count destinations) (count arguments))
                 (every? some? destinations)
                 (= (count destinations) (count (distinct destinations)))
                 (= #{:evaluations :commits} (set (keys plan)))
                 (vector? (:evaluations plan)) (vector? (:commits plan))
                 (= (count arguments) (count (:evaluations plan)) (count (:commits plan))))
    (reject! :transfer-interface []))
  (let [source-ids (mapv core/code-id arguments)]
    (doseq [[i binding] (map-indexed vector (:evaluations plan))]
      (when-not (and (= #{:temporary :expression} (set (keys binding)))
                     (= i (:temporary binding))
                     (= (nth source-ids i) (core/code-id (:expression binding))))
        (reject! :transfer-evaluation [:evaluations i])))
    (doseq [[i commit] (map-indexed vector (:commits plan))]
      (when-not (and (= #{:destination :temporary} (set (keys commit)))
                     (= i (:temporary commit)) (= (nth destinations i) (:destination commit)))
        (reject! :transfer-commit [:commits i])))
    {:version :ordered-transfer-v1 :arity (count arguments) :destinations destinations
     :argument-ids source-ids :plan-id (core/code-id plan)}))

(defn inspect!
  "Validate direct entry, fixed arity, self use only in tail position and no
   self transfer across a function/handler/staging boundary. Other operations
   retain their source structure and need separate semantic admission. Requires
   uniquely named binders as produced by ir/named; quotes are opaque."
  [t]
  (let [self (first (:names t)) f (first (:inits t)) entry (:body t)
        parameters (:params f)
        self? #(and (= :local (:op %)) (= self (:name %)))]
    (when-not (and (= :letrec (:op t)) (= 1 (count (:names t)))
                   (= 1 (count (:inits t))) (symbol? self)
                   (= :fn (:op f)) (false? (:rest? f))
                   (nat-int? (:arity f)) (vector? parameters)
                   (= (:arity f) (count parameters)) (every? symbol? parameters)
                   (= (count parameters) (count (distinct parameters)))
                   (not (some #{self} parameters))
                   (= :app (:op entry)) (self? (:fn entry))
                   (vector? (:args entry)) (= (:arity f) (count (:args entry))))
      (reject! :direct-entry []))
    (let [backedges (atom []) exits (atom [])]
      (letfn [(walk [node path tail? barrier?]
                (let [child #(walk %1 (into path %2) false barrier?)
                      args #(doseq [[i a] (map-indexed vector (:args node))] (child a [:args i]))
                      exit! #(when tail? (swap! exits conj {:path path :node node}))]
                  (case (:op node)
                    :quote (exit!)
                    :local (do (when (self? node) (reject! :escaping-self path)) (exit!))
                    :resolve (exit!)
                    :let (do (child (:init node) [:init])
                             (walk (:body node) (conj path :body) tail? barrier?))
                    :if (do (child (:test node) [:test])
                            (walk (:then node) (conj path :then) tail? barrier?)
                            (walk (:else node) (conj path :else) tail? barrier?))
                    :loop-check (do (args)
                                    (doseq [[i v] (map-indexed vector (:live node))] (child v [:live i]))
                                    (walk (:body node) (conj path :body) tail? barrier?))
                    :app (if (self? (:fn node))
                           (do (when (or (not tail?) barrier?) (reject! :non-tail-self-call path))
                               (when-not (and (vector? (:args node)) (= (count parameters) (count (:args node))))
                                 (reject! :backedge-arity path))
                               (args)
                               (swap! backedges conj {:path path :node node
                                                     :transfer (transfer parameters (:args node))}))
                           (do (child (:fn node) [:fn]) (args) (exit!)))
                    (:prim :numeric-guard) (do (args)
                                              (doseq [[i v] (map-indexed vector (:live node))] (child v [:live i]))
                                              (exit!))
                    :specialize (do (child (:fn node) [:fn]) (args) (exit!))
                    :perform (do (when (:target node) (child (:target node) [:target])) (args) (exit!))
                    :fn (do (walk (:body node) (conj path :body) false true) (exit!))
                    ;; ir/named intentionally leaves staged syntax opaque;
                    ;; its indices cannot be interpreted as this lexical level.
                    (:code :esc) (reject! :staging-boundary path)
                    :letrec (do (doseq [[i init] (map-indexed vector (:inits node))]
                                  (walk init (into path [:inits i]) false true))
                                (walk (:body node) (conj path :body) tail? true))
                    :handle (do (doseq [[name clause] (:clauses node)]
                                  (walk clause (into path [:clauses name]) false true))
                                (when (:return node) (walk (:return node) (conj path :return) false true))
                                (walk (:body node) (conj path :body) tail? true))
                    (reject! :unknown-control path))))]
        ;; Entry arguments may read surrounding locals, but must not retain or
        ;; invoke the new self binding before the admitted direct entry.
        (doseq [[i a] (map-indexed vector (:args entry))] (walk a [:body :args i] false false))
        (walk (:body f) [:inits 0 :body] true false)
        {:source t :self self :function f :parameters parameters :body (:body f)
         :entry {:path [:body] :node entry :transfer (transfer parameters (:args entry))}
         :backedges @backedges :exits @exits}))))

(defn view
  "Return a structural view, or nil for an ordinary unsupported loop."
  [t]
  (try (inspect! t)
       (catch clojure.lang.ExceptionInfo ex
         (if (= :unsupported-loop (:reason (ex-data ex))) nil (throw ex)))))
