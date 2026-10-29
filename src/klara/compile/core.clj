(ns klara.compile.core
  "World definition -> installable tested executable. Obligations: guard
  every assumption, fail closed before effects, preserve T0 fallback.
  Certificates record differential-test provenance, not a proof or a
  claim that compilation tests arbitrary user code."
  (:require [klara.compile.ir :as ir] [klara.compile.inline :as inline]
            [klara.compile.hof :as hof]
            [klara.compile.pe :as pe] [klara.compile.escape :as escape]
            [klara.compile.speculate :as speculate]
            [klara.compile.emit :as emit] [klara.compile.unbox :as unbox]
            [klara.core :as c]
            [klara.eval :as ev] [klara.stage :as stage] [klara.world :as w]))

(stage/register-checker! :klara.compile/tested
  (fn [exe] (when-not (and (= :tested (get-in exe [:certificate :kind]))
                           (= "s17-1" (get-in exe [:certificate :checker-version]))
                           (seq (:pass-log exe)) (fn? (:run exe))) :invalid-tested-executable)))

(def ^:dynamic *compiling* #{})

(def scalar-ops
  ;; Closed over canonical scalar inputs/results. No collection protocols,
  ;; host callbacks, authority or ambient operations in this licensed region.
  '#{+ - * / inc dec < > <= >= = not})

(defn context-only? [term dependencies]
  (and (every? :context-only? dependencies)
       (every? (fn [t]
                 (case (:op t)
                   :prim (contains? scalar-ops (:name t))
                   :quote (ev/inert-scalar? (:datum t))
                   :perform (some? (:target t))
                   true))
               (ir/nodes term))))

(defn compile-def
  ([world sym] (compile-def world sym {}))
  ([world sym {:keys [fuel inline-fuel] :or {fuel 10 inline-fuel 4}}]
   (when (*compiling* sym) (emit/unsupported nil "recursive world call requires a trampoline"))
   (binding [*compiling* (conj *compiling* sym)]
   (let [start (System/nanoTime) basis (if (instance? klara.world.World world) (w/snapshot world) world)
         e (w/entry* basis sym) f (:value e)]
     (when-not (and (= :def (:kind e)) (ev/closure? f) (empty? (ev/closure-locals f))
                    (not (w/pending? basis e))
                    (or (nil? (ev/closure-basis f)) (identical? basis (ev/closure-basis f))))
       (emit/unsupported (:term e) "definition must be a current, closed function"))
     (let [source (ev/closure-term f) cid (c/code-id source)
           s (speculate/run (ir/named source) cid)
           i (inline/run (:term s) basis inline-fuel)
           h (hof/run (:term i))
           k1 (ir/lower (:term h))
           p (pe/run k1 fuel) a (escape/run (:term p)) q (pe/run (:term a) fuel)
           callees (distinct (keep #(when (and (= :app (:op %)) (= :resolve (get-in % [:fn :op])))
                                     (get-in % [:fn :id])) (ir/nodes (:term q))))
           ;; Validate the whole fallback region, including transitive calls.
           ;; This rules out capturing operations behind a compiled host frame.
           dependencies (mapv #(compile-def basis % {:fuel fuel :inline-fuel inline-fuel}) callees)
           _ (when-not (every? #(= :s12-v1 (:abi %)) dependencies)
               (emit/unsupported nil "callee requires a different control ABI"))
           reads (into (:guards i) (mapcat #(filter (fn [g] (= :world (first g))) (:guards %))) dependencies)
           reads (into reads (map (fn [sym] [:world sym (:value-id (w/entry* basis sym))])) callees)
           collection-guards (hof/collection-guards (:term q))
           layouts (into {} (keep (fn [exe]
                                    (when (:return-layout exe)
                                      [(:name exe) (:return-layout exe)])) dependencies))
           out (emit/run (:term q) reads layouts)
           guards (into #{[:captures []] [:statics []] [:unhandled #{:exn/raise}]
                          [:arity (:arity source)]} reads)
           guards (into (cond-> (into (into guards collection-guards) (:guards h)) (pos? (:changes h)) (conj [:unhandled #{:host/call :host/var}]))
                        (mapcat #(filter (fn [g] (contains? #{:unhandled :host-root} (first g))) (:guards %))) dependencies)
           cert (-> (stage/certify cid guards :klara.compile/tested
                                  {:suite "test/klara/compile" :obligation :T0-observational-equivalence})
                    (assoc :kind :tested :checker-version "s17-1"
                           :frame-states (when (seq (:frame-states s))
                                           (stage/frame-states-digest {:generic source :frame-states (:frame-states s)}))) (dissoc :digest))]
       (merge out {:context-only? (context-only? (:term q) dependencies)
                   :return-layout (unbox/return-layout (:term q))
                   :generic source
                   :frame-states (when (seq (:frame-states s)) (:frame-states s))
                   :name sym :code-id cid :guards guards :ir (:term q)
                   :certificate (assoc cert :digest (stage/digest cert))
                   :allocation-analysis (:bindings a) :liveness (:liveness a)
                   :allocations-removed (:allocations-removed a)
                   :compile-ms (/ (- (System/nanoTime) start) 1e6)
                   :pass-log [{:pass :speculate :sites (count (:frame-states s))}
                              {:pass :inline :changes (:changes i)}
                              {:pass :lower :hof-rewrites (:changes h) :classes (frequencies (keep :class (ir/nodes k1)))}
                              {:pass :pe :rounds (:rounds p) :fuel-exhausted? (:fuel-exhausted? p)}
                              {:pass :escape :allocations-removed (:allocations-removed a)}
                              {:pass :pe :rounds (:rounds q) :fuel-exhausted? (:fuel-exhausted? q)}
                              {:pass :emit :backend :clojure}]}))))))

(alter-var-root #'compile-def (requiring-resolve 'klara.compile.affine-erase/wrap-compiler)) ; S10: isolated affine erasure hook
