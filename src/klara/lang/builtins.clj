(ns klara.lang.builtins
  "The registry of runtime-provided guest names (spec/L0-core.md#surface).

  Guest namespaces such as klara.world are not loaded from files: their
  names are registered here by the runtime. An entry is one of
    {:kind :intrinsic :fn (fn [machine-state args] state)}  needs the machine
    {:kind :host :fn f}                                     an ordinary function
    {:kind :special}                                        handled by the expander
    {:kind :macro :fn (fn [form env] form')}                a host-side macro")

(defonce registry (atom {}))

(defn register! [q entry] (swap! registry assoc q entry) q)

(defn lookup [q] (get @registry q))

(defn runtime-ns? [ns-sym]
  (contains? #{"klara.stage" "klara.world" "klara.effect" "klara.job" "klara.account" "klara.code" "klara.proof" "klara.jit" "klara.profile"
               "klara.compiler.kernel" "klara.kernel"}
             (str ns-sym)))

;; ---------------------------------------------------------------------------
;; Trusted host functions (L0.surface.resolve, L4.check.prim)

(def unsupported
  "Clojure names rejected with L0.surface.unsupported."
  '#{binding set! var alter-var-root intern eval deftype defprotocol
     extend-type extend-protocol reify gen-class case* monitor-enter monitor-exit
     with-redefs with-redefs-fn definterface proxy load load-file require use
     import refer find-var resolve ns-resolve future pmap agent send send-off})

(def pure-host
  "clojure.core functions the checker may evaluate on constants (L4.check.prim).
   Deterministic, no effects, no mutable results."
  '#{+ - * / quot rem mod inc dec < > <= >= = == not= not zero? pos? neg? even? odd?
     identity max min abs compare
     list vector hash-map array-map hash-set cons first second rest next seq empty? count nth get
     assoc dissoc conj concat vec str keyword symbol name namespace subs
     contains? keys vals peek pop into merge select-keys update get-in assoc-in
     nil? some? true? false? number? integer? int? double? float? ratio? string? keyword? symbol? map? vector?
     seq? coll? fn? boolean? set? sequential? distinct? reverse
     inc' dec' +' -' *' bit-and bit-or bit-xor bit-shift-left bit-shift-right})

(def mutating-host
  "Host functions that mutate their first argument (L3.job.host-mutation)."
  '#{swap! reset! swap-vals! reset-vals! vswap! vreset! compare-and-set!})
