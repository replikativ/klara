(ns klara.compile.subject
  "Opaque reference subjects and descriptive observation/evidence summaries.
   Prototype contracts do not establish unrestricted host contextual equality."
  (:require [klara.code :as code] [klara.core :as core]
            [klara.eval :as ev] [klara.world :as world]))

(def core-contract :klara/core-values-v1)
(def scalar-contract :klara/scalar-values-v1)
(def private-contract :klara/private-values-v1)

(defn contract-info [contract]
  (when-not (contains? #{core-contract scalar-contract private-contract} contract)
    (throw (ex-info "unsupported observation contract" {:reason :unsupported-contract})))
  {:id contract :status :experimental-projection
   :included [:admitted-values :numeric-classes :selected-failures :declared-effect-order]
   :not-established [:unrestricted-host-identity :arbitrary-metadata :full-contextual-equivalence]
   :not-observed [:physical-allocation :timing]})

(deftype Subject [source root contract])
(defmethod print-method Subject [_ out] (.write ^java.io.Writer out "#<optimization-subject>"))
(defn subject? [x] (instance? Subject x))
(defn source [^Subject x] (.-source x))
(defn reference-root [^Subject x] (.-root x))
(defn contract [^Subject x] (.-contract x))

(defn closed
  "Capture the reference root for a closed Code subject. No arbitrary
   observation map is accepted. Stronger host contracts remain unsupported."
  [root source]
  (when-not (and (code/code? source) (code/closed? source))
    (throw (ex-info "subject requires closed Code" {:reason :unsupported-region})))
  (Subject. source root core-contract))

(defn describe [^Subject subject]
  (let [term (code/s->core (code/code-term (source subject)))]
    {:source-id (core/code-id term)
     :interface (select-keys term [:arity :rest?])
     :reference-world {:version (:version (reference-root subject))
                       :version-is-validity-token? false}
     :contract (contract-info (contract subject))}))

(defn executable-summary [exe]
  (let [checker (get-in exe [:certificate :checker])
        contract (case checker
                   :klara.compile/staged-scalar scalar-contract
                   :klara.compile/inferred-affine private-contract
                   core-contract)]
    {:source-id (:code-id exe) :interface (select-keys (:generic exe) [:arity :rest?])
     :contract (contract-info contract)
     :evidence {:checker checker :kind (get-in exe [:certificate :kind])
                :complete-semantic-proof? false
                :runtime-premises (frequencies (map first (:guards exe)))
                :checked-recipe-count (count (:checked-edges exe))}
     :memory {:ownership-checked? (or (= checker :klara.compile/inferred-affine)
                                     (= :private-accumulator (get-in exe [:private-region :kind])))
              :host-alias-isolation? false :replayability-established? false}}))

(defn current-function
  "Return a current closed definition's closure, or nil. Admission only;
   callers retain their own budgets, diagnostics and semantic checkers."
  [root entry]
  (let [f (:value entry)]
    (when (and (= :def (:kind entry)) (ev/closure? f)
               (empty? (ev/closure-locals f)) (not (world/pending? root entry))
               (or (nil? (ev/closure-basis f)) (identical? root (ev/closure-basis f))))
      f)))
