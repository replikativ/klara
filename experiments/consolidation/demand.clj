(ns consolidation.demand
  "Map-only prefix specialization. Whole-vector totality licenses changes in
   forcing order; unknown/partial tails and unknown sequence adapters decline.
   Core/List/JVM correspondence and the eraser remain tested bridges."
  (:require [consolidation.demand-model :as model] [consolidation.interval :as interval]
            [ansatz.kernel.env :as env] [klara.code :as code]
            [klara.fusion.kernel :as k]
            [klara.core :as c] [klara.compile.staged :as staged]
            [klara.compile.strict-fold :as fold] [klara.eval :as ev]
            [klara.stage :as stage] [klara.authority :as authority]))

(def version "total-prefix-1")
(def bootstrap @model/proof-state)
(def roots
  (into #{[:host-root 'klara.core/prims c/prims]}
        (for [op '[map mapv take reduce +]]
          [:host-root (symbol "clojure.core" (name op)) @(ns-resolve 'clojure.core op)])))
(defn- decline! [check] (throw (ex-info (name check) {:reason :unsupported-demand :check check})))
(defn- call [op & args] (apply c/perform nil :host/call (c/quote* (symbol "clojure.core" (name op))) args))
(defn- var+ [] (c/perform nil :host/var (c/quote* 'clojure.core/+)))
(defn source-term [polynomial prefix kind]
  (c/lam 1 (call 'reduce (var+) (c/quote* 0)
                 (call 'take (c/quote* prefix) (call kind polynomial (c/local 0))))))
(defn target-term [polynomial prefix]
  (c/lam 1 (call 'reduce (c/lam 2 (c/prim '+ (c/local 1) (:body polynomial))) (c/quote* 0)
                 (call 'take (c/quote* prefix) (c/local 0)))))

(defn inspect [source]
  (let [term (code/s->core (code/code-term source))
        take-node (get-in term [:body :args 3]) map-node (get-in take-node [:args 2])
        prefix (get-in take-node [:args 1 :datum]) polynomial (get-in map-node [:args 1])
        kind (some-> map-node :args first :datum name symbol)]
    (when-not (and (code/closed? source) (instance? Long prefix) (<= 0 prefix)
                   (instance? Long (get-in term [:body :args 2 :datum]))
                   (#{'map 'mapv} kind) (= term (source-term polynomial prefix kind)))
      (decline! :source-interface))
    (c/assert-wf! polynomial)
    (when-not (and (= :fn (:op polynomial)) (= 1 (:arity polynomial)) (not (:rest? polynomial)))
      (decline! :polynomial-interface))
    {:source term :polynomial polynomial :prefix prefix :kind kind}))

(defn check-request [{:keys [source target domain]}]
  (when-not (and (code/code? source) (code/code? target) (code/closed? target)
                 (instance? Long (:max-count domain)) (<= 0 (:max-count domain)))
    (decline! :request-interface))
  (when-not (every? #(stage/guard-holds? % {}) roots) (decline! :host-root))
  (let [{:keys [polynomial prefix] :as source-info} (inspect source)
        actual-target (code/s->core (code/code-term target))
        expected (target-term polynomial prefix)]
    (when-not (and (= expected actual-target) (= (c/code-id expected) (c/code-id actual-target)))
      (decline! :endpoint-mismatch))
    (let [bounds (interval/certify (:body polynomial) (:max-x domain) Long/MAX_VALUE)
          total (interval/certify (c/prim '* (c/quote* (:max-count domain)) (c/quote* (long (:upper bounds)))) 0 Long/MAX_VALUE)
          witness (model/sum-witness bounds prefix)]
      (assoc source-info :target actual-target :bounds bounds :fold-bound total :witness witness))))

(defn- guards [domain native]
  (stage/compose-entry-guards
    (into roots #{[:captures []] [:statics []] [:arity 1]
                  [:unhandled #{:host/call :host/var :exn/raise}]
                  [:arg 0 [:bounded-nat-vector (:max-count domain) (:max-x domain)]]})
    (:guards native)))

(stage/register-checker! :klara.compile/demand-prefix
 (fn [exe]
   (try
     (let [request (:request exe) checked (check-request request) native (:native-executable exe)
           expected-lowering (fold/lower (:target checked))]
       (when-not (and (= version (get-in exe [:certificate :checker-version]))
                      (= :proved-total-prefix-with-tested-bridges (get-in exe [:certificate :kind]))
                      (= (:code-id exe) (c/code-id (:source checked))) (= (:generic exe) (:source checked))
                      (= (:target exe) (:target checked)) (= (:lowering exe) expected-lowering)
                      (= (:generic native) (:target expected-lowering)) (nil? (stage/check-certificate native))
                      (= (:guards exe) (guards (:domain request) native))
                      (= (:request-digest exe) (stage/digest request))
                      (= (:request-digest exe) (get-in exe [:certificate :request-digest]))
                      (= (get-in exe [:witness :goal]) (get-in checked [:witness :goal]))
                      (= (get-in exe [:witness :goal-sha256]) (get-in checked [:witness :goal-sha256]))
                      (= (get-in exe [:witness :proof-sha256]) (k/expr-hash (get-in exe [:witness :proof])))
                      (env/verifies? @model/proof-state (get-in checked [:witness :goal]) (get-in exe [:witness :proof]))
                      (identical? (:run exe) (:invoke1 exe)) (instance? clojure.lang.IFn$OL (:invoke1 exe)))
         :invalid-demand-prefix))
     (catch Exception _ :invalid-demand-prefix))))

(defn prepare [root request]
  (binding [authority/*store* (authority/new-store) ev/*entry-hook* nil ev/*direct-hook* nil ev/*context-hook* nil
            ev/*outer-k* [] ev/*fiber* nil]
    (let [checked (check-request request) compiled (fold/prepare root (:target request))
          native (.-executable ^klara.compile.staged.Prepared (:candidate compiled))
          gs (guards (:domain request) native) cid (c/code-id (:source checked)) digest (stage/digest request)
          worker (fn ^long [xs] (long (fold/project (:lowering compiled) ((:invoke1 native) xs))))
          cert (-> (stage/certify cid gs :klara.compile/demand-prefix
                                  {:obligation :total-finite-map-prefix :bridges :tested-core-machine-and-eraser})
                   (dissoc :digest) (assoc :kind :proved-total-prefix-with-tested-bridges
                                         :checker-version version :request-digest digest))
          exe {:generic (:source checked) :code-id cid :target (:target checked) :request request :request-digest digest
               :native-executable native :lowering (:lowering compiled) :guards gs
               :witness (:witness checked) :run worker :invoke1 worker
               :certificate (assoc cert :digest (stage/digest cert))}]
      (staged/prevalidate
        (klara.compile.staged.Prepared. (:source request) exe
          {:code-id cid :demand {:outputs (:prefix checked) :map-only true :license :whole-vector-totality}
           :executor :primitive-prefix-fold :native-info (:info compiled)
           :bounds (:bounds checked) :fold-bound (:fold-bound checked)
           :witness (select-keys (:witness checked) [:goal-sha256 :proof-sha256]) :bridges :tested})))))

(ev/register-reference-handler! :stage/prepare-demand
 (fn [[request] environment]
   (try (prepare (:basis environment) request)
        (catch clojure.lang.ExceptionInfo ex
          {:status :declined :reason (or (:reason (ex-data ex)) :unsupported-demand)
           :check (:check (ex-data ex))}))))
