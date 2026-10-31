(ns klara.compile.inline-check
  "Independent indexed correspondence check for local-call elimination.
   No producer freshening/substitution is used. Hosted adapter, not a proof
   of the full Core evaluator or JVM backend."
  (:require [klara.compile.budget :as budget] [klara.core :as core]))

(def version "indexed-inline-1")
(defn- reject! [check]
  (throw (ex-info "local-call syntax correspondence rejected"
                  {:reason :local-call-plan :check check})))

(defn- children-at [f t depth]
  (case (:op t)
    (:quote :local :resolve) t
    :fn (update t :body #(f % (+ depth (:arity t))))
    :let (-> t (update :init #(f % depth)) (update :body #(f % (inc depth))))
    :letrec (let [d (+ depth (count (:inits t)))]
              (-> t (update :inits #(mapv (fn [x] (f x d)) %)) (update :body #(f % d))))
    :app (-> t (update :fn #(f % depth)) (update :args #(mapv (fn [x] (f x depth)) %)))
    :prim (update t :args #(mapv (fn [x] (f x depth)) %))
    :if (-> t (update :test #(f % depth)) (update :then #(f % depth)) (update :else #(f % depth)))
    (reject! :indexed-control)))

(defn decode
  "Decode the admitted named grammar, checking unique binders and lexical scope.
   Optional preorder positions mark selected helper lets for indexed elimination."
  ([b term] (decode b term []))
  ([b term positions]
   (when-not (and (vector? positions) (every? #(and (integer? %) (<= 0 %)) positions)
                  (= (count positions) (count (distinct positions)))) (reject! :selected-positions))
   (let [names (atom #{}) seen (atom #{}) index (atom -1) selected (set positions)]
     (letfn [(bind! [xs]
               (when-not (and (vector? xs) (every? symbol? xs)
                              (= (count xs) (count (distinct xs)))
                              (not-any? @names xs)) (reject! :binder-freshness))
               (swap! names into xs) xs)
             (go [t env]
               (budget/charge! b :work 1)
               (let [at (swap! index inc) chosen? (contains? selected at)
                     _ (when chosen?
                         (when-not (and (= :let (:op t)) (= :fn (get-in t [:init :op])))
                           (reject! :selected-binding))
                         (swap! seen conj at))
                     child #(go % env)
                     out (case (:op t)
                           :quote (core/quote* (:datum t))
                           :resolve (core/resolve* (:id t))
                           :local (let [i (.lastIndexOf ^java.util.List env (:name t))]
                                    (when (neg? i) (reject! :lexical-scope))
                                    (core/local (- (count env) i 1)))
                           :fn (let [ps (bind! (:params t))]
                                 (when-not (and (not (:rest? t)) (integer? (:arity t))
                                                (= (:arity t) (count ps))) (reject! :binder-arity))
                                 (core/lam (:arity t) false (go (:body t) (into env ps))))
                           :let (let [s (first (bind! [(:name t)])) init (child (:init t))]
                                  (core/let1 init (go (:body t) (conj env s))))
                           :letrec (let [ss (bind! (:names t)) e (into env ss)]
                                     (when-not (= (count ss) (count (:inits t))) (reject! :binder-arity))
                                     (core/letrec (mapv #(go % e) (:inits t)) (go (:body t) e)))
                           :app (core/app* (child (:fn t)) (mapv child (:args t)))
                           :prim (apply core/prim (:name t) (mapv child (:args t)))
                           :if (core/if* (child (:test t)) (child (:then t)) (child (:else t)))
                           (reject! :indexed-control))]
                 (if chosen? (with-meta out {::selected true}) out)))]
       (let [out (go term [])]
         (when-not (= selected @seen) (reject! :selected-positions))
         (core/assert-wf! out) out)))))

(defn check!
  "Check selected helper elimination with de Bruijn shifts. Arguments are bound
   once, left to right; each later argument is lifted over prior temporary lets.
   Captured helper locals are lifted over intervening caller binders."
  [b source target positions]
  (let [indexed (decode b source positions) actual (decode b target) calls (atom 0)]
    (letfn [(shift [t cutoff amount]
              (budget/charge! b :work 1)
              (if (= :local (:op t))
                (cond-> t (>= (:index t) cutoff) (update :index + amount))
                (children-at #(shift %1 %2 amount) t cutoff)))
            (remove-helper [t depth f]
              (budget/charge! b :work 1)
              (cond
                (= :local (:op t))
                (cond (= (:index t) depth) (reject! :escaping-helper)
                      (> (:index t) depth) (update t :index dec) :else t)
                (and (= :app (:op t)) (= (core/local depth) (:fn t)))
                (do (when-not (= (:arity f) (count (:args t))) (reject! :call-arity))
                    (swap! calls inc)
                    (let [args (mapv #(remove-helper % depth f) (:args t))
                          body (shift (:body f) (:arity f) depth)]
                      (reduce (fn [body [i arg]] (core/let1 (shift arg 0 i) body))
                              body (reverse (map-indexed vector args)))))
                :else (children-at #(remove-helper %1 %2 f) t depth)))
            (expand [t]
              (budget/charge! b :work 1)
              (let [out (children-at (fn [child _] (expand child)) t 0)]
                (if (::selected (meta t))
                  (remove-helper (:body out) 0 (:init out)) out)))]
      (let [expected (expand indexed)]
        (core/assert-wf! expected)
        ;; CodeIds preserve literal numeric representations, unlike Clojure =.
        (when-not (= (core/code-id expected) (core/code-id actual)) (reject! :indexed-residual))
        {:version version :source-id (core/code-id indexed) :target-id (core/code-id actual)
         :calls @calls :binding-check :unique-lexical-binders
         :relation :indexed-ordered-helper-elimination :evidence :hosted-checked}))))
