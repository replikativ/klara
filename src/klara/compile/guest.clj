(ns klara.compile.guest
  "World-managed transfer policy and producer, with a reviewed bootstrap.
   Edited services remain pure and stepped; output never selects its checker."
  (:require [klara.compile.budget :as budget] [klara.compile.loop :as transfer]
            [klara.compile.service :as service]             [klara.eval :as ev]
            [klara.core :as core] [klara.expand :as expand] [klara.stage :as stage]
            [klara.world :as world]))

(def transfer-source
  '(fn [destinations arguments]
     (loop [i 0 evaluations [] commits []]
       (if (< i (count arguments))
         (recur (inc i)
                (conj evaluations {:temporary i :expression (nth arguments i)})
                (conj commits {:destination (nth destinations i) :temporary i}))
         {:evaluations evaluations :commits commits}))))

(defonce ^:private source-term (delay (expand/expand-expr transfer-source world/empty-root)))

(defonce ^:private seeds (atom {}))

(def policy-symbol 'klara.compiler/transfer-policy)
(def producer-symbol 'klara.compiler/transfer)
(def policy-source '(fn [request] 'klara.compiler/transfer))

(defn bootstrap!
  "Explicitly install missing compiler definitions in one world publication.
   Existing edits are preserved. Loading user code never implicitly does this."
  [w]
  (service/publish-missing! w [[producer-symbol transfer-source] [policy-symbol policy-source]]))

(defn- room? [b]
  (or (nil? b)
      (and (>= (- (get (:limits b) :work Long/MAX_VALUE)
                  (get (budget/usage b) :work 0)) 2048)
           (>= (- (get (:limits b) :bytes Long/MAX_VALUE)
                  (get (budget/usage b) :bytes 0)) 16384)
           (>= (- (get (:limits b) :emissions Long/MAX_VALUE)
                  (get (budget/usage b) :emissions 0)) 2)
           (room? (:parent b)))))

(defn- inert-input!
  "Bound exact data before running count/nth/conj in the service. Named Core
   expressions are copied opaquely by guest code but checked by the adapter."
  [b destinations arguments]
  (when-not (and (= clojure.lang.PersistentVector (class destinations))
                 (= clojure.lang.PersistentVector (class arguments))
                 (= (count destinations) (count arguments))
                 (<= (count arguments) 20) (every? symbol? destinations)
                 (= (count destinations) (count (distinct destinations))))
    (throw (ex-info "invalid transfer service input" {:reason :unsupported-region})))
  (service/data! b [destinations arguments]))

(defn- seed-producer
  "Return the actual compiled guest producer when funded, otherwise the
   existing hosted producer. Both outputs pass the independent plan checker.
   Compilation uses the same baseline pipeline with bootstrap recursion off."
  [b]
  (fn [destinations arguments]
    (budget/charge! b :work (+ 1 (* 8 (count arguments))))
    (let [source @source-term
          key [:baseline-direct-loop-1 (core/code-id source)]
          exe (or (get @seeds key)
                  (when (room? b)
                    (locking seeds
                      (or (get @seeds key)
                          (let [exe ((requiring-resolve 'klara.compile.baseline/compile-source)
                                     world/empty-root source {:guest-transfer? false :budget b})]
                            (stage/validate-executable exe)
                            (swap! seeds assoc key exe) exe)))))]
      (when (and exe (not-every? #(stage/guard-holds? % {})
                                (filter #(= :host-root (first %)) (:guards exe))))
        (throw (ex-info "transfer service primitive root changed" {:reason :stale-host-root})))
      (with-meta (if exe ((:run exe) destinations arguments) (transfer/transfer destinations arguments))
        (cond-> {:producer (if exe :klara-baseline :hosted)}
          exe (assoc :producer-code-id (:code-id exe)))))))

(defn producer
  "Resolve policy and producer against exactly root. Only an exact reviewed
   source match may use the native seed. Compiler reads are provenance, not
   runtime guards: the independent checker fixes transfer semantics regardless
   of which compiler world produced the plan."
  ([b] (producer b world/empty-root))
  ([b root]
   (let [seed (seed-producer b)]
     (fn [destinations arguments]
       (inert-input! b destinations arguments)
       (if-not (world/entry* root policy-symbol)
         (seed destinations arguments)
         (let [request {:arity (long (count arguments)) :phase :transfer :backend :clojure}
               decision (service/invoke b root policy-symbol [request] 4096)
               choice (:value decision)
               policy-reads (:compiler-reads decision)
               _ (when-not (or (= :hosted choice) (symbol? choice))
                   (throw (ex-info "transfer policy declined or returned an invalid choice"
                                   {:reason :compiler-policy-declined :choice choice})))
               reviewed? (when (symbol? choice)
                           ;; Validate current closure and its complete pure
                           ;; dependency closure before even considering native.
                           (service/validate! b root choice))
               entry (when (symbol? choice) (world/entry* root choice))
               source (when entry (core/code-id (ev/closure-term (:value entry))))
               exact? (= source (core/code-id @source-term))
               result (cond
                        (= :hosted choice) {:value (transfer/transfer destinations arguments)
                                            :compiler-reads #{} :mode :world-hosted}
                        exact? {:value (seed destinations arguments)
                                :compiler-reads reviewed? :mode :world-baseline}
                        :else (assoc (service/invoke b root choice [destinations arguments] 16384)
                                     :mode :world-stepped))
               plan (:value result)]
           (service/data! b plan)
           ;; Reject before attaching metadata, and again at the emitter's
           ;; consumption boundary. A returned plan is never executable code.
           (transfer/check-transfer! destinations arguments plan)
           (with-meta plan
             (merge (meta plan)
                    {:producer (if (and exact? (= :hosted (:producer (meta plan))))
                                 :world-hosted (:mode result))
                     :producer-symbol (when (symbol? choice) choice)
                     :producer-code-id source
                     :policy-symbol policy-symbol
                     :policy-code-id (core/code-id (ev/closure-term (:value (world/entry* root policy-symbol))))
                     :service-transitions (+ (:transitions decision) (or (:transitions result) 0))
                     :compiler-reads (into policy-reads (:compiler-reads result))}))))))))
