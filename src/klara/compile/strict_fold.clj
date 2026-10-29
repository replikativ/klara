(ns klara.compile.strict-fold
  "Lower a strict vector fold to the common counted-loop IR. No mathematical
   rewrite or map fusion is licensed here. The input-layout guard is required.
   Lowering correspondence is tested; source arithmetic remains checked."
  (:require [klara.code :as code]
            [klara.compile.analysis :as analysis]
            [klara.compile.infer-affine :as ia]
            [klara.compile.ir :as ir]
            [klara.compile.staged :as staged]
            [klara.core :as c]
            [klara.eval :as ev]
            [klara.stage :as stage]))

(def version "strict-vector-fold-3")
(defn- fail [message] (throw (ex-info message {:reason :strict-fold})))
(defn- loc [n] {:op :local :name n})
(defn- bind [n value body] {:op :let :name n :init value :body body})

(defn lower [source]
  (c/assert-wf! source)
  (let [t (ir/named source) b (:body t) [op f init input] (:args b)
        prefix? (and (= :perform (:op input)) (nil? (:target input)) (= :host/call (:name input))
                     (= 3 (count (:args input)))
                     (= (c/quote* 'clojure.core/take) (first (:args input)))
                     (= :quote (get-in input [:args 1 :op]))
                     (instance? Long (get-in input [:args 1 :datum])))
        prefix (when prefix? (get-in input [:args 1 :datum]))
        xs (if prefix? (get-in input [:args 2]) input)]
    (when-not (and (= :fn (:op t)) (= 1 (:arity t)) (not (:rest? t))
                   (= :perform (:op b)) (nil? (:target b)) (= :host/call (:name b))
                   (= (c/quote* 'clojure.core/reduce) op) (= 4 (count (:args b)))
                   (= (loc (first (:params t))) xs) (= :quote (:op init)))
      (fail "expected a reduce with explicit literal seed over the input vector"))
    (let [seed (:datum init) scalar? (instance? Long seed)
          initial (if scalar? [seed] seed)
          _ (when-not (and (= clojure.lang.PersistentVector (class initial))
                           (seq initial) (every? #(instance? Long %) initial))
              (fail "expected Long or nonempty Long-vector seed"))
          n (gensym "size") i (gensym "index") acc (gensym "acc") x (gensym "element") self (gensym "fold")
          value (if scalar? (c/prim 'nth (loc acc) (c/quote* 0)) (loc acc))
          update (cond
                   (and (= :fn (:op f)) (= 2 (:arity f)) (not (:rest? f)))
                   (ir/substitute (:body f) (zipmap (:params f) [value (loc x)]))
                   (and scalar? (= :perform (:op f)) (= :host/var (:name f))
                        (#{'clojure.core/+ 'clojure.core/*} (:datum (first (:args f)))))
                   (c/prim (symbol (name (:datum (first (:args f))))) value (loc x))
                   :else (fail "expected an inline binary step or scalar +/*"))
          update (if scalar? (c/prim 'assoc (loc acc) (c/quote* 0) update) update)
          step (bind x (c/prim 'nth xs (loc i))
                     (c/app (loc self) (c/prim 'inc (loc i)) update))
          step (if prefix? (c/if* (c/prim '< (loc i) (c/quote* prefix)) step (loc acc)) step)
          loop {:op :letrec :names [self]
                :inits [{:op :fn :arity 2 :rest? false :params [i acc]
                         :body (c/if* (c/prim '< (loc i) (loc n))
                                     step (loc acc))}]
                :body (c/app (loc self) (c/quote* 0) (c/quote* initial))}
          ;; Give the common converter scalar/vector prefix initializers.
          start (gensym "start") seed-name (gensym "seed")
          loop (assoc loop :body (c/app (loc self) (loc start) (loc seed-name)))
          target (analysis/indexed (assoc t :body
                                         (bind n (c/prim 'count xs)
                                               (bind start (c/quote* 0)
                                                     (bind seed-name (c/quote* initial) loop)))))]
      {:version version :source-id (c/code-id source) :target target
       :target-id (c/code-id target) :projection (if scalar? :singleton-scalar :identity)
       :prefix prefix})))

(defn prepare [root source]
  (let [term (code/s->core (code/code-term source)) lowering (lower term)
        candidate (ia/prepare root (code/->code (code/core->s (:target lowering)))
                              {:parameter-layouts [:long-vector]})]
    {:candidate candidate :lowering lowering
     :info (staged/prepared-info candidate)}))

(defn project [lowering result]
  (case (:projection lowering) :singleton-scalar (nth result 0) :identity result))

(def ^:private reduce-root @#'clojure.core/reduce)
(def ^:private take-root @#'clojure.core/take)
(defn- guards [native lowering]
  (cond-> (conj (:guards native) [:host-root 'clojure.core/reduce reduce-root]
                [:unhandled #{:host/call :host/var :exn/raise}])
    (some? (:prefix lowering)) (conj [:host-root 'clojure.core/take take-root])))

(stage/register-checker!
 :klara.compile/strict-fold
 (fn [exe]
   (try
     (let [lowering (lower (:generic exe)) native (:native-executable exe)]
       (when-not (and (= version (get-in exe [:certificate :checker-version]))
                      (= :tested (get-in exe [:certificate :kind]))
                      (= (:lowering exe) lowering) (= (:code-id exe) (:source-id lowering))
                      (= (:generic native) (:target lowering))
                      (= (:guards exe) (guards native lowering))
                      (nil? (stage/check-certificate native)) (fn? (:run exe)) (fn? (:invoke1 exe)))
         :invalid-strict-fold))
     (catch Exception _ :invalid-strict-fold))))

(defn prepare-specialization [root source]
  (let [start (System/nanoTime) {:keys [candidate lowering info]} (prepare root source)
        native (.-executable ^klara.compile.staged.Prepared candidate)
        gs (guards native lowering) cid (:source-id lowering)
        cert (-> (stage/certify cid gs :klara.compile/strict-fold
                                {:obligation :strict-fold-to-owned :bridges :tested})
                 (dissoc :digest) (assoc :kind :tested :checker-version version))
        exe {:code-id cid :generic (code/s->core (code/code-term source)) :guards gs
             :lowering lowering :native-executable native
             :run (fn [xs] (project lowering ((:run native) xs)))
             :invoke1 (fn [xs] (project lowering ((:invoke1 native) xs)))
             :certificate (assoc cert :digest (stage/digest cert))}]
    (klara.compile.staged.Prepared. source exe
      {:executor :private-array :evidence :tested-lowering :lowering lowering :native-info info
       :compile-ms (/ (- (System/nanoTime) start) 1e6)})))

(ev/register-reference-handler!
 :stage/prepare-fold
 (fn [[source] env]
   (try (prepare-specialization (:basis env) source)
        (catch clojure.lang.ExceptionInfo ex
          {:status :declined :reason (or (:reason (ex-data ex)) :strict-fold)
           :diagnostic (ex-message ex)}))))
