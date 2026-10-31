(ns klara.compile.investment
  "One explicit funded investment attempt over the existing candidate lifecycle.
   Policy is ordinary bounded guest code. Timings guide investment, never
   semantic admission. Pure replay subset only; no native wall-clock preemption."
  (:require [klara.authority :as authority] [klara.code :as code]
            [klara.compile.budget :as budget] [klara.compile.funding :as funding]
            [klara.compile.service :as service] [klara.compile.staged :as staged]
            [klara.core :as core] [klara.defs :as defs] [klara.eval :as ev]
            [klara.stage :as stage] [klara.world :as world]))

(def policy-symbol 'klara.compiler/investment)
(def policy-source
  '(fn [r]
     (if (if (<= (get r :remaining-calls) 0)
           true (> (get r :spent-ns) (get r :allowance-ns)))
       {:action :stop}
       (if (= (get r :phase) :unseen)
         {:action :probe}
         (if (= (get r :phase) :reference)
           (if (> (get r :predicted-gross-ns) (get r :future-cost-ns))
             {:action :prepare} {:action :stop})
           (if (= (get r :phase) :prepared)
             {:action :probe}
             (if (= (get r :phase) :compared)
               (if (> (get r :measured-gross-ns) (get r :publication-estimate-ns))
                 {:action :install} {:action :stop})
               {:action :stop})))))))

(defn bootstrap! [w]
  (service/publish-missing! w [[policy-symbol policy-source]])
  w)

(def defaults {:remaining-calls 0 :allowance-ns 100000000 :preparation-estimate-ns 30000000
               :comparison-estimate-ns 2000000 :publication-estimate-ns 100000
               :candidate-fraction 0.5 :safety-factor 2.0 :probe-pairs 3 :fuel 16384})
(defn- options! [options]
  (let [o (merge defaults options)]
    (doseq [k [:remaining-calls :allowance-ns :preparation-estimate-ns
               :comparison-estimate-ns :publication-estimate-ns]]
      (when-not (and (integer? (k o)) (<= 0 (k o) (if (= k :remaining-calls) 1000000 1000000000000)))
        (throw (ex-info "invalid investment estimate" {:reason :invalid-investment :field k}))))
    (when-not (and (number? (:candidate-fraction o)) (<= 0.0 (:candidate-fraction o) 1.0)
                   (number? (:safety-factor o)) (<= 1.0 (:safety-factor o) 100.0)
                   (integer? (:probe-pairs o)) (<= 1 (:probe-pairs o) 7)
                   (integer? (:fuel o)) (<= 1 (:fuel o) 16384))
      (throw (ex-info "invalid investment limits" {:reason :invalid-investment}))) o))
(defn- median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))
(defn- bounded-ns [n] (long (min 1000000000000000000 (max 0 (double n)))))

(defn- snapshot-cache [state]
  ;; Only immutable publication data is shared. Hooks and counters belong to
  ;; the new cache, rather than closing over the operational cache being copied.
  (let [cache (stage/make-cache)]
    (swap! cache merge (select-keys state [:entries :ordered :next-install])) cache))

(defn attempt!
  "Probe current execution, optionally prepare/validate in an isolated world,
   compare complete calls in replay forks, then ask policy whether to publish.
   Every policy action is phase-checked; publication uses the original checker.
   A shared Funding bounds sponsored work/emissions. :allowance-ns stops future
   phases after measured spend exceeds it; an individual host phase may overrun.
   remaining-calls is a forecast of future calls AFTER these extra probe calls."
  [cache root symbol args job options]
  (when-not (and (funding/funding? job) (symbol? symbol) (vector? args))
    (throw (ex-info "invalid investment invocation" {:reason :invalid-investment})))
  (let [o (options! options) b (funding/counter job) policy-root (or (:policy-root o) root)
        policy (get o :policy policy-symbol) f (defs/lookup root symbol)
        initial-state @cache baseline-cache (snapshot-cache initial-state)
        proposed-cache (snapshot-cache initial-state)
        state (atom {:phase :unseen :spent-ns 0 :events []})
        timed (fn [phase f]
                (when (> (:spent-ns @state) (:allowance-ns o))
                  (throw (ex-info "investment time allowance spent" {:reason :investment-time-allowance})))
                (let [start (System/nanoTime)]
                  (try (f)
                       (finally
                         (let [elapsed (- (System/nanoTime) start)]
                           (swap! state (fn [s] (-> s (update :spent-ns + elapsed)
                                                   (update :events conj {:phase phase :elapsed-ns elapsed})))))))))
        run (fn [candidate?]
              (let [replica (world/fork (world/make-world root)) basis (world/snapshot replica)]
                (binding [authority/*store* (authority/new-store) ev/*basis* basis ev/*mint* basis
                          ev/*fiber* (world/fiber replica) ev/*outer-k* []]
                  (let [start (System/nanoTime)
                        value (stage/with-cache (if candidate? proposed-cache baseline-cache)
                                (ev/call-value f args))]
                    (when-not (identical? basis (world/snapshot replica))
                      (throw (ex-info "replay changed its reference world" {:reason :investment-replay})))
                    {:value value :ns (- (System/nanoTime) start)}))))
        probe (fn [candidate? witness]
                (let [samples
                      (mapv (fn [i]
                              ;; Reserve reference-transition-equivalent sponsorship,
                              ;; not a claim about actual native instructions or CPU.
                              (budget/charge! b :work (* (:transitions witness) (if candidate? 2 1)))
                              (let [order (if candidate?
                                            (if (even? i) [:reference :candidate] [:candidate :reference]) [:reference])]
                                (into {} (for [k order]
                                           (let [r (run (= k :candidate))]
                                             (when-not (= (core/code-id (core/quote* (:value witness)))
                                                          (core/code-id (core/quote* (:value r))))
                                               (throw (ex-info "probe observation disagrees" {:reason :investment-replay})))
                                             [k (dissoc r :value)]))))) (range (:probe-pairs o)))]
                  {:samples samples :reference-ns (median (map #(get-in % [:reference :ns]) samples))
                   :candidate-ns (when candidate? (median (map #(get-in % [:candidate :ns]) samples)))}))]
    (try
      (loop [steps 0 witness nil candidate nil]
        (when (>= steps 6) (throw (ex-info "investment action limit" {:reason :investment-actions})))
        (let [{:keys [phase spent-ns reference comparison]} @state
              request (merge (select-keys o [:remaining-calls :allowance-ns :publication-estimate-ns])
                             {:phase phase :spent-ns spent-ns
                              :predicted-gross-ns (bounded-ns (* (:remaining-calls o) (or (:reference-ns reference) 0)
                                                                              (- 1.0 (:candidate-fraction o))))
                              :future-cost-ns (bounded-ns (* (:safety-factor o)
                                                            (+ (:preparation-estimate-ns o) (:comparison-estimate-ns o)
                                                               (:publication-estimate-ns o))))
                              :measured-gross-ns (bounded-ns (* (:remaining-calls o)
                                                               (- (or (:reference-ns comparison) 0)
                                                                  (or (:candidate-ns comparison) 0))))})
              decision (:value (timed :policy #(service/invoke b policy-root policy [request] 4096)))
              action (:action decision)]
          (when-not (and (map? decision) (= #{:action} (set (keys decision)))
                         (case action :stop true :probe (contains? #{:unseen :prepared} phase)
                           :prepare (= :reference phase) :install (= :compared phase) false))
            (throw (ex-info "invalid investment action" {:reason :invalid-investment-action :phase phase})))
          (swap! state update :events conj {:phase :decision :action action :request request})
          ;; The host cap cannot be bypassed by editing the policy. Time is only
          ;; checked between phases; resource counters charge within preparation.
          (if (or (= action :stop) (> (:spent-ns @state) (:allowance-ns o)))
            (swap! state assoc :status :stopped :reason (if (= action :stop) :policy :time-allowance))
            (case action
              :probe
              (let [witness (or witness
                                (timed :eligibility
                                  #(do
                                     ;; A pure original does not sandbox an arbitrary
                                     ;; host-supplied cache implementation.
                                     (doseq [exe (stage/executables baseline-cache)]
                                       (budget/charge! b :work 1)
                                       (when-not (= :klara.compile/baseline (get-in exe [:certificate :checker]))
                                         (throw (ex-info "replay requires baseline compiler candidates"
                                                         {:reason :investment-replay-cache}))))
                                     (service/invoke b root symbol args (:fuel o)))))
                    r (timed :probe #(probe (= phase :prepared) witness))]
                (swap! state assoc (if (= phase :prepared) :comparison :reference) r
                       :phase (if (= phase :prepared) :compared :reference))
                (recur (inc steps) witness candidate))
              :prepare
              (let [replica (world/fork (world/make-world root)) reference-root (world/snapshot replica)
                    source (code/->code (code/core->s (ev/closure-term f)))
                    r (timed :preparation #(staged/request reference-root source
                                              (assoc (:preparation-options o) :job job :policy-root policy-root)))]
                (if (= :prepared (:status r))
                  (let [checked (timed :validation #(staged/prevalidate (:candidate r)))
                        installed (timed :probe-installation #(staged/install! proposed-cache root checked))
                        admitted? (when (= :installed (:status installed))
                                    (timed :candidate-admission
                                      #(binding [ev/*outer-k* []]
                                         (identical? (:run (stage/enter proposed-cache f [] args root []))
                                                     (:run (.-executable ^klara.compile.staged.Prepared checked))))))]
                    (swap! state assoc :candidate-admitted? (boolean admitted?))
                    (if admitted?
                      (do (swap! state assoc :phase :prepared) (recur (inc steps) witness checked))
                      (swap! state assoc :status :declined :reason (or (:reason installed) :guard-miss-or-shadowed))))
                  (swap! state assoc :status (:status r) :reason (:reason r))))
              :install
              (let [_ (when-not (identical? (:entries initial-state) (:entries @cache))
                        (throw (ex-info "portfolio changed during investment" {:reason :investment-stale-portfolio})))
                    result (timed :publication #(staged/install! cache root candidate))]
                (swap! state assoc :status (:status result) :reason (:reason result) :phase :finished))))))
      (catch clojure.lang.ExceptionInfo e
        (swap! state assoc :status (case (:reason (ex-data e))
                                     :budget-exhausted :exhausted :investment-time-allowance :stopped :rejected)
               :reason (:reason (ex-data e))))
      (catch Exception e
        ;; Reference arithmetic failures and host compilation/IO failures still
        ;; return the charged attempt. Do not catch fatal VM errors.
        (when (instance? InterruptedException e) (.interrupt (Thread/currentThread)))
        (swap! state assoc :status :failed :reason :investment-exception
               :error-class (.getName (class e)) :error (.getMessage e))))
    (assoc @state :probe-cache-stats (stage/stats proposed-cache)
           :reference-cache-stats (stage/stats baseline-cache) :usage (funding/usage job) :remaining-calls (:remaining-calls o)
           :forecast (select-keys o [:preparation-estimate-ns :comparison-estimate-ns :publication-estimate-ns
                                     :candidate-fraction :safety-factor])
           :limits [:explicit-checkpoint :pure-inert-replay-subset :shared-host-jit-gc-clock
                    :timing-not-semantic-evidence :soft-time-cap :no-native-preemption
                    :finite-horizon-forecast :no-automatic-retirement])))
