(ns klara.compile.core
  "World definition -> installable tested executable. Obligations: guard
  every assumption, fail closed before effects, preserve T0 fallback.
  Certificates record differential-test provenance, not a proof or a
  claim that compilation tests arbitrary user code."
  (:require [klara.compile.ir :as ir] [klara.compile.inline :as inline]
            [klara.compile.pe :as pe] [klara.compile.escape :as escape]
            [klara.compile.emit :as emit] [klara.core :as c]
            [klara.eval :as ev] [klara.stage :as stage] [klara.world :as w]))

(stage/register-checker! :klara.compile/tested
  (fn [exe] (when-not (and (= :tested (get-in exe [:certificate :kind]))
                           (= "s8-1" (get-in exe [:certificate :checker-version]))
                           (seq (:pass-log exe)) (fn? (:run exe))) :invalid-tested-executable)))

(defn compile-def
  ([world sym] (compile-def world sym {}))
  ([world sym {:keys [fuel inline-fuel] :or {fuel 10 inline-fuel 4}}]
   (let [start (System/nanoTime) basis (if (instance? klara.world.World world) (w/snapshot world) world)
         e (w/entry* basis sym) f (:value e)]
     (when-not (and (= :def (:kind e)) (ev/closure? f) (empty? (ev/closure-locals f))
                    (not (w/pending? basis e)))
       (emit/unsupported (:term e) "definition must be a current, closed function"))
     (let [source (ev/closure-term f) cid (c/code-id source)
           i (inline/run (ir/named source) basis inline-fuel)
           k1 (ir/lower (:term i))
           p (pe/run k1 fuel) a (escape/run (:term p)) q (pe/run (:term a) fuel)
           out (emit/run (:term q))
           guards (into #{[:captures []] [:statics []] [:unhandled #{:exn/raise}]} (:guards i))
           cert (-> (stage/certify cid guards :klara.compile/tested
                                  {:suite "test/klara/compile" :obligation :T0-observational-equivalence})
                    (assoc :kind :tested :checker-version "s8-1") (dissoc :digest))]
       (merge out {:run (fn [& args]
                                ;; Definition-time execution must record reads
                                ;; erased by inlining, even on a cache hit.
                                (doseq [[_ s h] (:guards i)] (w/note-read! [:value s h]))
                                (apply (:run out) args))
                   :name sym :code-id cid :guards guards :ir (:term q)
                   :certificate (assoc cert :digest (stage/digest cert))
                   :allocation-analysis (:bindings a) :liveness (:liveness a)
                   :allocations-removed (:allocations-removed a)
                   :compile-ms (/ (- (System/nanoTime) start) 1e6)
                   :pass-log [{:pass :inline :changes (:changes i)}
                              {:pass :lower :classes (frequencies (keep :class (ir/nodes k1)))}
                              {:pass :pe :rounds (:rounds p) :fuel-exhausted? (:fuel-exhausted? p)}
                              {:pass :escape :allocations-removed (:allocations-removed a)}
                              {:pass :pe :rounds (:rounds q) :fuel-exhausted? (:fuel-exhausted? q)}
                              {:pass :emit :backend :clojure}]})))))
