(ns consolidation.checked-pipeline
  "S24 mathematical edges through S23's actual preparation/publication path.
   Executors use T0 or the shared strict-fold/owned primitive-array path.
   Lowering and representation correspondence remain tested bridges."
  (:require [proof-staging :as ps]
            [consolidation.interval :as interval]
            [consolidation.fold-model :as fold-model]
            [klara.authority :as authority]
            [klara.compile.staged :as staged]
            [klara.compile.strict-fold :as fold]
            [klara.core :as core]
            [klara.eval :as ev]
            [klara.stage :as stage]
            [klara.world :as w]))

(def version "checked-chain-5")

;; Initialize proof declarations before operational preparation effects exist.
(def bootstrap
  (let [start (System/nanoTime)]
    @interval/proof-state
    @fold-model/proof-state
    {:milliseconds (/ (- (System/nanoTime) start) 1e6)}))

(defn bounds-evidence [request]
  (mapv (fn [endpoint]
          (let [expression (ps/polynomial-body endpoint (:domain request))
                proof (interval/certify expression (get-in request [:domain :max-x]) Long/MAX_VALUE)
                total (interval/certify
                        (core/prim '* (core/quote* (get-in request [:domain :max-count]))
                                   (core/quote* (long (:upper proof)))) 0 Long/MAX_VALUE)]
            {:endpoint-id (core/code-id (ps/core-term endpoint))
             :element-upper (:upper proof) :sum-upper (:upper total)
             :element-proof proof :capacity-product-proof total}))
        (cons (:source request) (:targets request))))

(defn- decline! [check message]
  (throw (ex-info message {:reason :unsupported-region :check check})))

(defn check-request
  "Rebuild every proof goal from actual Code endpoints, then kernel-check the
   composed theorem. Recipes propose theorem instances, never acceptance."
  [{:keys [source targets steps domain]}]
  (when-not (and (vector? targets) (seq targets) (vector? steps)
                 (= (count targets) (count steps)))
    (decline! :chain-interface "one recipe per target is required"))
  (let [edges
        (loop [from source targets targets steps steps out []]
          (if-let [to (first targets)]
            (let [{:keys [kind coefficients]} (first steps)
                  edge (case kind
                         :numeric (do (when-not (= 3 (count coefficients))
                                        (decline! :numeric-interface "quadratic coefficients required"))
                                      (ps/numeric-edge from to coefficients domain))
                         :fusion (ps/fusion-edge from to domain)
                         (decline! :unknown-specializer "unknown checked specializer"))]
              (recur to (next targets) (next steps) (conj out edge)))
            out))]
    (reduce ps/compose edges)))

(defn- execution-kind [request]
  (let [kind (get request :executor :T0-vector)]
    (when-not (#{:T0-vector :private-array} kind)
      (decline! :executor "unknown executor"))
    kind))

(defn- guards [edge native]
  (let [domain [:bounded-nat-vector (get-in edge [:domain :max-count]) (get-in edge [:domain :max-x])]
        unhandled #{:host/var :host/call :exn/raise}
        outer (into (set ps/reference-host-roots)
                    #{[:captures []] [:statics []] [:arity 1]
                      [:unhandled unhandled] [:arg 0 domain]})]
    (stage/compose-entry-guards outer (:guards native))))

(stage/register-checker!
 :klara.compile/checked-chain
 (fn [exe]
   (try
     (let [edge (check-request (:request exe))
           _ (bounds-evidence (:request exe))
           kind (execution-kind (:request exe))
           native (:native-executable exe)
           lowering (when (= kind :private-array) (fold/lower (ps/core-term (:to edge))))]
       (when-not (and (= version (get-in exe [:certificate :checker-version]))
                      (= :proved-equality-with-tested-bridges (get-in exe [:certificate :kind]))
                      (= (:code-id exe) (:source-id edge))
                      (= (:generic exe) (ps/core-term (:from edge)))
                      (= (:target exe) (ps/core-term (:to edge)))
                      (= (:guards exe) (guards edge native))
                      (= (:request-digest exe) (stage/digest (:request exe)))
                      (= (:request-digest exe) (get-in exe [:certificate :request-digest]))
                      (= (:executor exe) kind)
                      (if native (instance? clojure.lang.IFn$OL (:invoke1 exe)) (nil? (:invoke1 exe)))
                      (if lowering
                        (and (= (:lowering exe) lowering)
                             (= (:generic native) (:target lowering))
                             (fold-model/verify-witness? edge (:private-witness exe))
                             (nil? (stage/check-certificate native)))
                        (nil? native))
                      (fn? (:run exe)))
         :invalid-checked-chain))
     (catch Exception _ :invalid-checked-chain))))

(defn prepare [_root request]
  (binding [authority/*store* (authority/new-store)
            ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
            ev/*outer-k* [] ev/*fiber* nil w/*reads* nil]
    (let [start (System/nanoTime)
          edge (check-request request) bounds (bounds-evidence request)
          target (ps/core-term (:to edge))
          proof-ms (/ (- (System/nanoTime) start) 1e6)
          kind (execution-kind request)
          compiled (when (= kind :private-array) (fold/prepare _root (:to edge)))
          native (when compiled (.-executable ^klara.compile.staged.Prepared (:candidate compiled)))
          private-witness (when native (fold-model/witness edge))
          gs (guards edge native) cid (:source-id edge) digest (stage/digest request)
          cert (-> (stage/certify cid gs :klara.compile/checked-chain
                                 {:obligation :bounded-pure-equality
                                  :bridges :tested-elaboration-bounds-and-T0})
                   (dissoc :digest)
                   (assoc :kind :proved-equality-with-tested-bridges
                          :checker-version version :request-digest digest))
          exe {:code-id cid :generic (ps/core-term (:from edge)) :target target
               :request request :request-digest digest :guards gs
               :executor kind :native-executable native :lowering (:lowering compiled)
               :private-witness private-witness
               :invoke1 (when native (fn ^long [xs] (long (fold/project (:lowering compiled) ((:invoke1 native) xs)))))
               :run (if native
                      (fn [xs] (fold/project (:lowering compiled) ((:run native) xs)))
                      (fn [xs]
                      ;; No recursive entry into this cache when endpoints are
                      ;; identical; execute the pure target through the T0 bridge.
                      (binding [ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil]
                        (ev/call-value (ev/run target {:basis w/empty-root}) [xs]))))
               :certificate (assoc cert :digest (stage/digest cert))}
          info {:code-id cid :target-id (:target-id edge) :guards gs
                :evidence :kernel-equality :bounds-evidence bounds :bridges :tested
                :executor kind :steps (mapv :kind (:steps request))
                :lowering (:lowering compiled) :native-info (:info compiled)
                :private-witness (select-keys private-witness [:source-id :target-id :goal-sha256 :proof-sha256])
                :shared-bootstrap-ms (:milliseconds bootstrap)
                :proof-and-bounds-ms proof-ms :compile-ms (/ (- (System/nanoTime) start) 1e6)}]
      (staged/prevalidate (klara.compile.staged.Prepared. (:source request) exe info)))))

(ev/register-reference-handler!
 :stage/prepare-checked
 (fn [[request] env]
   (try (prepare (:basis env) request)
        (catch clojure.lang.ExceptionInfo e
          {:status :declined :reason (or (:reason (ex-data e)) :unsupported-proof)
           :check (:check (ex-data e)) :diagnostic (ex-message e)}))))
